import Leanux.Proofs.WG.Index.ReachedSchedulerSource
import Leanux.Proofs.WG.Index.TimerProductCoreSource
import Leanux.Proofs.WG.Index.ReachedWorkersSource
import Leanux.Proofs.WG.Queues.HolderEntryDeferred
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedDeferred
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem observed_ready {α : Type} (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (observed : RxHistory.Obs α) (action : Leanux.M α)
    (account : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe observed)
    (structural : ∀ initial, PrefixPreserves (fun _ w=>BaseCoherence.view w.wg=initial) (fun _=>True) observed)
    (erase : ErasesPrefix observed action)
    (ready : Preserves (fun w : World=>TimerCore.Ready w.wg) action) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe observed := by
  apply Reached.aux_pair _ initial loans before account
  intro w h pre result v run
  have base := (structural (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at base
  have kept := (hoare_iff_run _ _ _).mp ready w result v
    ⟨pre.1.2.2,pre.2.2⟩ ((erase w h).symm.trans run)
  exact ⟨BaseCoherence.transport pre.2.1 base,kept.2⟩

theorem saved_spec (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit getDevSavedAudit)
      (fun d h w=>Reached.Aux initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  intro w h pre
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.saved_spec)
      w h pre.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit getDevSavedAudit) w h).1 with
  | error stop => trivial
  | ok out =>
    rw [run] at post
    have same := (ProjectedAction.iff_run _ _ _).mp
      (liftWG_sameProductStore getDev getDev_sameWGStore) w out.1 out.2
      ((RxHistory.audit_erases getDevSavedAudit_erases w h).symm.trans run)
    exact ⟨⟨post.1,(Reached.aux_store same pre).2⟩,post.2⟩

theorem saved (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit getDevSavedAudit) :=
  ((saved_spec initial loans before).consequence (fun _ _ pre=>pre) (fun _ _ _ pre=>pre.1)).preserves

theorem wheel_spec (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (d : Device) (j : UInt64) :
    PrefixEnsures
      (fun h w=>Reached.Aux initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      OwnerChecks.Safe (RxHistory.audit (wheelNextDueAudit d j))
      (fun _=>Reached.Aux initial loans before) := by
  intro w h pre
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.wheel_spec)
      d j w h ⟨pre.1.1,pre.2⟩
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit (wheelNextDueAudit d j)) w h).1 with
  | error stop => trivial
  | ok out =>
    rw [run] at post
    have actual := (RxHistory.audit_erases (wheelNextDueAudit_erases d j) w h).symm.trans run
    change Except.ok (TimerWheel.nextDue d j,w)=Except.ok (out.1,out.2) at actual
    have equal := congrArg (fun result=>result.map Prod.snd) actual
    simp only [Except.map,Except.ok.injEq] at equal
    exact ⟨post,equal ▸ pre.1.2⟩

theorem drained (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (what : String) (queues : List Bool) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (requireDrainedPrefix what queues)) :=
  ReachedScheduler.observed_store initial loans before _ _
    (HolderAuxDeferred.drained initial loans before what queues)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
    (PendingScheduler.requireDrained_store what queues)

theorem stepComplete (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (bucket : UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  ReachedScheduler.observed_store initial loans before _ _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.stepComplete) bucket)
    (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket))
    (PendingScheduler.requireStepComplete_store bucket)

theorem nothingDue (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (j : UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireNothingDueAudit j)) :=
  ReachedScheduler.observed_store initial loans before _ _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.nothingDue) j)
    (RxHistory.audit_erases (requireNothingDueAudit_erases j))
    (PendingScheduler.requireNothingDue_store j)

theorem timerDispatch (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (kind : Worker) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  observed_ready initial loans before _ _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.timerDispatch)
      kind pid timer entry prior)
    (fun initial=>(BaseCoherence.deferred_atoms initial).timer kind pid timer entry prior)
    (RxHistory.audit_erases (timerDispatchAudit_erases kind pid timer entry prior))
    (TimerCore.dispatch_ready kind pid timer entry prior)

theorem placeholderPass (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (j : UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  observed_ready initial loans before _ _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.placeholderPass) j)
    (fun initial=>(BaseCoherence.deferred_atoms initial).placeholder j)
    (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j))
    (TimerCore.placeholder_ready j)

theorem hooks (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    DriverTags.Deferred.HookContracts (Reached.Aux initial loans before) OwnerChecks.Safe
      (DriverTags.Deferred.originalHooks (fun {_} a=>a)) :=
  ⟨ReachedWorkers.send_observed initial loans before,ReachedWorkers.clear_observed initial loans before,
    timerDispatch initial loans before,placeholderPass initial loans before⟩

end Leanux.Proofs.WG.Index.ReachedDeferred
