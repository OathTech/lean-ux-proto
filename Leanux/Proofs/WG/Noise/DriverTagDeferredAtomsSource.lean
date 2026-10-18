import Leanux.Proofs.WG.Noise.DriverTagDeferredSource
import Leanux.Proofs.WG.Noise.DriverTagTimerProductSource
import Leanux.Proofs.WG.Noise.DriverTagDispatchSource

/-! Every old deferred atom has its own actual erasure and frame. Four
effectful callback slots remain explicit and are instantiated by real calls. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.DeferredCalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def old {α : Type} (observer : RxHistory.Obs α) : ProductObs α := DriverTags.discard observer

theorem atoms (entry : TagMap) : Deferred.QuietAtoms (StateInv entry) ValidHistory (fun {_} a => old a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro what queues
    exact discard_store entry _ _ (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
      (PendingScheduler.requireDrained_store what queues)
  · exact discard_store entry _ _ (RxHistory.audit_erases getDevSavedAudit_erases)
      (liftWG_sameProductStore getDev getDev_sameWGStore)
  · intro d j
    exact discard_store entry _ _ (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
      (SameView.pure _ _)
  · intro bucket
    exact discard_store entry _ _ (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket))
      (PendingScheduler.requireStepComplete_store bucket)
  · intro j
    exact discard_store entry _ _ (RxHistory.audit_erases (requireNothingDueAudit_erases j))
      (PendingScheduler.requireNothingDue_store j)
  · exact discard_store entry _ _ (RxHistory.mixed_erases requireIdleDevicePrefix_erases)
      PendingScheduler.requireIdleDevice_store
  · exact discard_store entry _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
      requireNoCryptWork_sameKernel
  · intro timer
    exact discard_store entry _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
      (timerWorker_sameKernel timer)
  · intro ticks
    exact discard_store entry _ _ (RxHistory.audit_erases (advanceAudit_erases ticks))
      (advance_sameKernel ticks)

theorem atoms_erases : Deferred.QuietErases (fun {_} a => old a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro what queues
    exact discard_erases _ _ (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
  · exact discard_erases _ _ (RxHistory.audit_erases getDevSavedAudit_erases)
  · intro d j
    exact discard_erases _ _ (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
  · intro bucket
    exact discard_erases _ _ (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket))
  · intro j
    exact discard_erases _ _ (RxHistory.audit_erases (requireNothingDueAudit_erases j))
  · exact discard_erases _ _ (RxHistory.mixed_erases requireIdleDevicePrefix_erases)
  · exact discard_erases _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
  · intro timer
    exact discard_erases _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
  · intro ticks
    exact discard_erases _ _ (RxHistory.audit_erases (advanceAudit_erases ticks))

def hooks : Deferred.Hooks DriverTagEvent :=
  ⟨Dispatch.runOneSendObserved,Dispatch.runOneClearObserved,
    fun worker pid timer wheel prior => liftPrefix (timerDispatchUnit worker pid timer wheel prior),
    fun j => liftPrefix (RxHistory.placeholderTimerPassSource j)⟩

theorem hooks_preserve (entry : TagMap) :
    Deferred.HookContracts (StateInv entry) ValidHistory hooks :=
  ⟨Dispatch.runOneSendObserved_preserves entry,Dispatch.runOneClearObserved_preserves entry,
    TimerProduct.dispatch_preserves entry,TimerProduct.placeholder_preserves entry⟩

theorem hooks_erase : Deferred.HookErases hooks :=
  ⟨Dispatch.runOneSendObserved_erases,Dispatch.runOneClearObserved_erases,
    fun _ _ _ _ _ => erasesPrefix_lift _,fun _ => erasesPrefix_lift _⟩

end Leanux.Proofs.WG.Noise.DriverTags.DeferredCalls

