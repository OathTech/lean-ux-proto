import Leanux.Proofs.WG.RetirementSecurity.HolderTimerEnvironmentKeys

/-! Exact key accounting through the original recorded wheel loop. The saved
peer receipt remains tied to each actual wheel lookup; the native callback,
clear work and crypt drain are proved on their actual entry states. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits Std.Do

theorem timer_store (a : Leanux.M α) (frame : SameProductStore a) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ entry=>entry.1.2.1.safe)
    (fun _ _ _ same entry=>store entry same) frame

theorem timer_join {action : RxHistory.Obs α} {native : Leanux.M α}
    (old : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (erase : ErasesPrefix action native)
    (keeps : Preserves (HolderTimerKeys.ProductReady temporary locals active) native) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe action := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := old w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have ready := (hoare_iff_run _ _ _).mp keeps w out.1 out.2 ⟨entry.2,entry.1.2.2⟩
      ((erase w h).symm.trans run)
    exact ⟨post,ready.1⟩

private theorem saved_spec : PrefixEnsures (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit)
    (fun d h w=>Inv initial loans before temporary locals active h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.saved_spec)
      w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.audit getDevSavedAudit) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have same := (ProjectedAction.iff_run _ _ _).mp (liftWG_sameProductStore getDev getDev_sameWGStore)
      w out.1 out.2 ((RxHistory.audit_erases getDevSavedAudit_erases w h).symm.trans run)
    exact ⟨⟨post.1,extra_store entry.2 same⟩,post.2⟩

private theorem saved : PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit) :=
  (saved_spec.consequence (fun _ _ entry=>entry) (fun _ _ _ entry=>entry.1)).preserves

private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w=>Inv initial loans before temporary locals active h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    OwnerChecks.Safe (RxHistory.audit (wheelNextDueAudit d j))
    (fun _=>Inv initial loans before temporary locals active) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.wheel_spec)
      d j w h ⟨entry.1.1,entry.2⟩
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.audit (wheelNextDueAudit d j)) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have same := (ProjectedAction.iff_run _ _ _).mp (SameView.pure productStoreView (TimerWheel.nextDue d j))
      w out.1 out.2 ((RxHistory.audit_erases (wheelNextDueAudit_erases d j) w h).symm.trans run)
    exact ⟨post,extra_store entry.1.2 same⟩

private theorem stepComplete (bucket : UInt64) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  timer_join ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.stepComplete) bucket)
    (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket)) (HolderTimerKeys.step_complete bucket)

private theorem nothingDue (j : UInt64) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit (requireNothingDueAudit j)) :=
  timer_join ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.nothingDue) j)
    (RxHistory.audit_erases (requireNothingDueAudit_erases j)) (HolderTimerKeys.nothing_due j)

private theorem timerDispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  timer_join ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.timerDispatch) kind pid timer entry prior)
    (RxHistory.audit_erases (timerDispatchAudit_erases kind pid timer entry prior))
    (HolderTimerKeys.dispatch kind pid timer entry prior)

private theorem placeholderPass (j : UInt64) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  timer_join ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.placeholderPass) j)
    (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j)) (HolderTimerKeys.placeholder j)

macro "holder_key_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence
    (P := Inv _ _ _ _ _ _) (Q := fun _ => Inv _ _ _ _ _ _) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "holder_key_timer_calls" : tactic => `(tactic| first
  | (rx_timer_head timerDispatchAudit; exact timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact send_one)
  | (rx_timer_head runOneClearWorkerAudit; exact clear_one)
  | (rx_timer_head RxHistory.runCryptWorkers; exact crypt)
  | (rx_timer_head RxHistory.runSendWorkers; exact send_all)
  | (rx_timer_head getWG; exact timer_store _ (fun initial => productGetWG_spec (fun s => s=initial)))
  | (rx_timer_head modifyWG; exact timer_store _ (fun initial => productModifyWG_spec (fun s => s=initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact timer_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl))
  | (rx_timer_head Env.peekNextSite; exact timer_store _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact timer_store _ deliverSent_sameKernel)
  | (rx_timer_head throw; exact timer_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run))
  | (audit_contract_head liftPrefix; exact timer_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.1.2.1.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => Inv _ _ _ _ _ _ h w) (hs := fun _ _ _ hi => hi.1.2.1.safe)))

/-- The exact saved getter precedes each wheel scan. Source dispatch, cleanup,
crypt work and stopping guards remain in the original record-driven loop. -/
theorem runTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (jHi : UInt64) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (holder_key_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (holder_key_timer_drop_saved; holder_key_timer_calls)
    | holder_key_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Inv initial loans before temporary locals active h w))
    | (holder_key_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (holder_key_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholder (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (jHi : UInt64) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact runTimers _ _ _ _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | holder_key_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Inv initial loans before temporary locals active h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

/-- Both record-driven and placeholder paths use the actual source clocks,
with the original end-of-wait check and no new timing assumption. -/
theorem idleTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe RxHistory.idleTimers := by
  have safe : ∀ h w, Inv initial loans before temporary locals active h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.1.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before temporary locals active h w → Inv initial loans before temporary locals active h v :=
    fun _ _ _ same hi => store hi same
  unfold RxHistory.idleTimers
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact runTimers _ _ _ _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _ _ _ _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _ => pure ())
       exact PrefixPreserves.bind (runTimers _ _ _ _) (fun _ => PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

theorem afterAdvance (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe RxHistory.afterAdvance := by
  have safe : ∀ h w, Inv initial loans before temporary locals active h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.1.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before temporary locals active h w → Inv initial loans before temporary locals active h v :=
    fun _ _ _ same hi => store hi same
  unfold RxHistory.afterAdvance
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact runTimers _ _ _ _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _ _ _ _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _ => pure ())
       exact PrefixPreserves.bind (runTimers _ _ _ _) (fun _ => PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
