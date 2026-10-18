import Leanux.Proofs.WG.Queues.HolderAuxSend
import Leanux.Proofs.WG.Queues.SlotTimers

/-! Strong timer composition on the original journal. The wheel scan consumes
its actual saved-peer receipt; no unconditional owner scan contract is assumed. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
variable {initial : Ledger} {loans : Reservations} {before : List RxHistory.Event}

private theorem store (a : Leanux.M α) (frame : SameProductStore a) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => HolderAuxiliary.store hi same) frame

private theorem audit (g : AuditM α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (account : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) (RxHistory.audit g))
    (owner : OwnerChecks.Preserves (RxHistory.audit g))
    (slots : Preserves (fun w : World => CurrentSlots.Inv w.wg) a) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.audit g) := by
  apply HolderAuxiliary.pair _ account owner
  intro w h hi x v run
  exact (hoare_iff_run _ _ _).mp slots w x v hi.2.2
    ((RxHistory.audit_erases erase w h).symm.trans run)

private theorem clearOne_slots : Preserves (fun w : World => CurrentSlots.Inv w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Removal.flushedClear pid)
    w.wg beforeWorker () v.wg v.ambient hi worker

private theorem clearOne : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit runOneClearWorkerAudit) :=
  audit _ _ runOneClearWorkerAudit_erases HolderTimerPhysical.atoms.clearOne
    OwnerDeferred.clearOne clearOne_slots

private theorem saved_spec : PrefixEnsures (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit)
    (fun d h w => HolderAuxiliary.Inv initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.saved_spec) w h hi.2.1
  have held := (HolderTimerPhysical.atoms.saved w h hi.1).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit getDevSavedAudit) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at held post
    have slots := (hoare_iff_run _ _ _).mp
      (CurrentSlots.product_store_preserves (liftWG_sameProductStore getDev getDev_sameWGStore))
      w out.1 out.2 hi.2.2 ((RxHistory.audit_erases getDevSavedAudit_erases w h).symm.trans run)
    exact ⟨⟨held,post.1,slots⟩,post.2⟩

private theorem saved : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit) :=
  (saved_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)).preserves

/-- The owner side is conditional on the saved getter receipt; the pure scan
retains the account and slots on its identical original execution. -/
private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w => HolderAuxiliary.Inv initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    OwnerChecks.Safe (RxHistory.audit (wheelNextDueAudit d j))
    (fun _ => HolderAuxiliary.Inv initial loans before) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.wheel_spec)
      d j w h ⟨hi.1.2.1,hi.2⟩
  have held := (HolderTimerPhysical.atoms.wheel d j w h hi.1.1).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit (wheelNextDueAudit d j)) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at held post
    have slots := (hoare_iff_run _ _ _).mp
      (CurrentSlots.product_store_preserves (SameView.pure productStoreView (TimerWheel.nextDue d j)))
      w out.1 out.2 hi.1.2.2 ((RxHistory.audit_erases (wheelNextDueAudit_erases d j) w h).symm.trans run)
    exact ⟨held,post,slots⟩

private theorem stepComplete (bucket : UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  audit _ _ (requireStepCompleteAudit_erases bucket) (HolderTimerPhysical.atoms.stepComplete bucket)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.stepComplete) bucket)
    (CurrentSlots.Timer.stepComplete bucket)

private theorem nothingDue (j : UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireNothingDueAudit j)) :=
  audit _ _ (requireNothingDueAudit_erases j) (HolderTimerPhysical.atoms.nothingDue j)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.nothingDue) j)
    (CurrentSlots.Timer.nothingDue j)

private theorem timerDispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  audit _ _ (timerDispatchAudit_erases kind pid timer entry prior)
    (HolderTimerPhysical.atoms.timer kind pid timer entry prior)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.timerDispatch) kind pid timer entry prior)
    (CurrentSlots.Timer.dispatch kind pid timer entry prior)

private theorem placeholderPass (j : UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  audit _ _ (RxHistory.placeholderTimerPass_erases j) (HolderTimerPhysical.atoms.placeholder j)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.placeholderPass) j)
    (CurrentSlots.Timer.placeholder j)

macro "aux_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence
    (P := HolderAuxiliary.Inv _ _ _) (Q := fun _ => HolderAuxiliary.Inv _ _ _) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "aux_timer_calls" : tactic => `(tactic| first
  | (rx_timer_head timerDispatchAudit; exact timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact HolderAuxSend.sendOne _ _ _)
  | (rx_timer_head runOneClearWorkerAudit; exact clearOne)
  | (rx_timer_head RxHistory.runCryptWorkers; exact HolderAuxDeferred.crypt _ _ _)
  | (rx_timer_head RxHistory.runSendWorkers; exact HolderAuxSend.runSendWorkers _ _ _)
  | (rx_timer_head getWG; exact store _ (fun initial => productGetWG_spec (fun s => s=initial)))
  | (rx_timer_head modifyWG; exact store _ (fun initial => productModifyWG_spec (fun s => s=initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl))
  | (rx_timer_head Env.peekNextSite; exact store _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (rx_timer_head throw; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run))
  | (audit_contract_head liftPrefix; exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.2.1.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => HolderAuxiliary.Inv _ _ _ h w) (hs := fun _ _ _ hi => hi.2.1.safe)))

/-- The exact saved getter precedes each wheel scan. Source dispatch, cleanup,
crypt work and stopping guards remain in the original record-driven loop. -/
theorem runTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (jHi : UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (aux_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (aux_timer_drop_saved; aux_timer_calls)
    | aux_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => HolderAuxiliary.Inv initial loans before h w))
    | (aux_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (aux_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholder (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (jHi : UInt64) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact runTimers _ _ _ _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | aux_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => HolderAuxiliary.Inv initial loans before h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

/-- Both record-driven and placeholder paths use the actual source clocks,
with the original end-of-wait check and no new timing assumption. -/
theorem idleTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.idleTimers := by
  have safe : ∀ h w, HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderAuxiliary.store hi same
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
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.afterAdvance := by
  have safe : ∀ h w, HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderAuxiliary.store hi same
  unfold RxHistory.afterAdvance
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact runTimers _ _ _ _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _ _ _ _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _ => pure ())
       exact PrefixPreserves.bind (runTimers _ _ _ _) (fun _ => PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

/-- Normal native returns use their exact original observer's output journal,
including every committed removal before the final completion check. -/
theorem runTimers_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : (Env.runTimers j).run w=.ok (result,v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix (RxHistory.runTimers j) w h).2 v := by
  have actual := (RxHistory.runTimers_erases j w h).trans run
  have post := (runTimers initial loans before j w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem placeholder_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : (Env.runTimersPlaceholder j).run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix (RxHistory.runTimersPlaceholder j) w h).2 v := by
  have actual := (RxHistory.runTimersPlaceholder_erases j w h).trans run
  have post := (runTimersPlaceholder initial loans before j w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem idle_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.idleTimers.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.idleTimers w h).2 v := by
  have actual := (RxHistory.idleTimers_erases w h).trans run
  have post := (idleTimers initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem afterAdvance_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.afterAdvance.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.afterAdvance w h).2 v := by
  have actual := (RxHistory.afterAdvance_erases w h).trans run
  have post := (afterAdvance initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

/-- All fourteen concrete deferred constructors retain the stronger domain.
The timer scan premise remains local to the actual saved getter above. -/
theorem deferred (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (call : EnvDeferredCall) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact HolderAuxDeferred.drained initial loans before what queues
  | idleDevice =>
    apply HolderAuxiliary.pair _ HolderTimerPhysical.atoms.idleDevice (OwnerDeferred.deferred .idleDevice)
    intro w h hi x v run
    cases x
    have actual := (RxHistory.mixed_erases requireIdleDevicePrefix_erases w h).symm.trans run
    exact (idleDevice_normal w v actual).1 ▸ hi.2.2
  | noCrypt =>
    exact audit _ _ (erasesPrefix_lift _) HolderTimerPhysical.atoms.noCrypt
      (OwnerDeferred.deferred .noCrypt) (CurrentSlots.product_store_preserves requireNoCryptWork_sameKernel)
  | crypt => exact HolderAuxDeferred.crypt initial loans before
  | sendOne => exact HolderAuxSend.sendOne initial loans before
  | clearOne => exact clearOne
  | sendAll => exact HolderAuxSend.runSendWorkers initial loans before
  | afterXmit => exact HolderAuxSend.afterXmit initial loans before
  | timerWorker timer =>
    exact audit _ _ (erasesPrefix_lift _) (HolderTimerPhysical.atoms.timerWorker timer)
      (OwnerDeferred.deferred (.timerWorker timer))
      (CurrentSlots.product_store_preserves (timerWorker_sameKernel timer))
  | timers j => exact runTimers initial loans before j
  | placeholder j => exact runTimersPlaceholder initial loans before j
  | idle => exact idleTimers initial loans before
  | advance ticks =>
    exact audit _ _ (advanceAudit_erases ticks) (HolderTimerPhysical.atoms.advance ticks)
      (OwnerDeferred.deferred (.advance ticks))
      (CurrentSlots.product_store_preserves (advance_sameKernel ticks))
  | afterAdvance => exact afterAdvance initial loans before

theorem deferred_normal (call : EnvDeferredCall) {result : call.Result} (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : call.original.run w=.ok (result,v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix (RxHistory.deferred call) w h).2 v := by
  have actual := (RxHistory.deferred_erases call w h).trans run
  have post := (deferred initial loans before call w h hi).choose_spec.2.2
  simpa only [actual] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers
