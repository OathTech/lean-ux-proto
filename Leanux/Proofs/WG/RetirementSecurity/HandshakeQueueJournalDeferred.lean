import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalDeferredBase

/-! Shared deferred work and wheel loops carry the actual validated input
queue together with history safety, retaining emitted history on Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option TransmitSecurity.Journal.Event}

macro "handshake_journal_deferred_step " c:ident : tactic => `(tactic| first
  | (nonce_product_head Driver.Hooks.deliver; exact deliver $c)
  | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished $c _)
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_wg _ (kernel getDev_sameWGStore))
  | (scheduler_preserve_at delTimer; exact product_wg _ (delTimer_cell _ _))
  | (scheduler_preserve_at Env.runOneSendWorker; exact product_lift _ _ _ (product_frame send_one_cell))
  | (nonce_product_head Driver.sendWorkerObserved
     exact send_one $c)
  | (scheduler_preserve_at Env.runOneClearWorker; exact clear_one)
  | (nonce_product_head Driver.clearWorkerObserved; exact clear_observed $c)
  | (scheduler_preserve_at Env.requireDrained; exact product_store _ (Nonce.Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact product_store _ (Nonce.Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact product_store _ (Nonce.Frames.nothing_due _))
  | (scheduler_preserve_at Driver.timerObserved; exact state_product (timer $c _ _))
  | (scheduler_preserve_at throw; exact product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact product_ambient _ _ _)
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

theorem crypt (c : Contracts Valid Safe hooks ρ) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.cryptObserved hooks) :=
  PrefixPreserves.bind (schedule c none) (fun _ => deliver c)

theorem send_workers (c : Contracts Valid Safe hooks ρ) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.sendWorkersObserved hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule c _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

theorem after_xmit (c : Contracts Valid Safe hooks ρ) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.afterXmitObserved hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt c)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers c)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

theorem timer_section (worker : Worker) {body : PrefixM E Unit}
    (safe : PrefixPreserves (ProductInv Valid Safe) Safe body) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _ _ _) (fun _ =>
      PrefixPreserves.bind (product_ambient _ _ _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.2) stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _ _ _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) stable worker safe)

theorem timers (c : Contracts Valid Safe hooks ρ) (jPass : UInt64) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.timersObserved hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt c)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (state_product (timer c _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

theorem placeholder_timers (c : Contracts Valid Safe hooks ρ) (jHi : UInt64) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.placeholderTimersObserved hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt c)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers c)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (state_product (timer c _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

theorem idle_timers (c : Contracts Valid Safe hooks ρ) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.idleTimersObserved hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers c _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers c _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

theorem after_advance (c : Contracts Valid Safe hooks ρ) :
    PrefixPreserves (ProductInv Valid Safe) Safe (Driver.afterAdvanceObserved hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers c _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers c _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected c _ _ _ _ _)
    | handshake_journal_deferred_step c

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
