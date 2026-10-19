import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalCallbacks

/-! Actual deferred source composition certifies every scheduler poll through
send-worker dispatch and wheel timer execution, retaining certificates on Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open OccurrenceStack Queues.RxCredits

theorem product_stable (h : List Journal.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (before : Inv [] h w) : Inv [] h v := by
  exact ⟨ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) before.1,before.2⟩

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe (liftPrefix action) :=
  product_lift action (kernel_predicate ready_kernel same)

theorem wg_read : ProductSafe (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe (liftPrefix getEnv) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run
  exact hi

theorem get_dev : Preserves (Ready [] []) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ before

theorem timer_selected (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (we : WheelEntry) :
    ProductSafe (Journal.hooks.timerSelected d j pid t we) := by
  apply join_history (hooks_safe.timerSelected d j pid t we)
  intro w h result v before run
  change (runPrefix (AuthenticatedEffects.TimerDispatch.scope Journal.Event.timerSelected d j pid t we (pure ())) w h).1 = _ at run
  simp only [AuthenticatedEffects.TimerDispatch.scope_run,runPrefix_pure] at run
  cases run
  exact before

macro "occurrence_journal_deferred_step" : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_native _ get_dev)
  | (scheduler_preserve_at delTimer; exact product_native _ (OccurrenceTimers.maintenance (.deleteTimer _ _)))
  | (scheduler_preserve_at Env.runOneSendWorker; exact send_one)
  | (nonce_product_head Driver.sendWorkerObserved
     rw [Driver.sendWorker_lift Journal.hooks rfl]
     exact send_one)
  | (scheduler_preserve_at Env.runOneClearWorker; exact clear_one)
  | (scheduler_preserve_at Env.requireDrained; exact product_store _ (Nonce.Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact product_store _ (Nonce.Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact product_store _ (Nonce.Frames.nothing_due _))
  | (scheduler_preserve_at Driver.timerObserved; exact state_product (timer_callback _ _))
  | (scheduler_preserve_at throw; exact product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; first
     | apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.2)
     | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.2))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem crypt :
    PrefixPreserves (Inv []) Safe (Driver.cryptObserved Journal.hooks) :=
  PrefixPreserves.bind (schedule none) (fun _ => product_store _ deliverSent_sameKernel)

theorem send_workers :
    PrefixPreserves (Inv []) Safe (Driver.sendWorkersObserved Journal.hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

theorem after_xmit :
    PrefixPreserves (Inv []) Safe (Driver.afterXmitObserved Journal.hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

theorem timer_section (worker : Worker) {body : PrefixM Journal.Event Unit}
    (safe : PrefixPreserves (Inv []) Safe body) :
    PrefixPreserves (Inv []) Safe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      PrefixPreserves.bind (product_ambient _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_stable worker safe)

theorem timers (jPass : UInt64) :
    PrefixPreserves (Inv []) Safe (Driver.timersObserved Journal.hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (state_product (timer_callback _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

theorem placeholder_timers (jHi : UInt64) :
    PrefixPreserves (Inv []) Safe (Driver.placeholderTimersObserved Journal.hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (state_product (timer_callback _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

theorem idle_timers :
    PrefixPreserves (Inv []) Safe (Driver.idleTimersObserved Journal.hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

theorem after_advance :
    PrefixPreserves (Inv []) Safe (Driver.afterAdvanceObserved Journal.hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | occurrence_journal_deferred_step

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
