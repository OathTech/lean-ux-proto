import Leanux.Proofs.WG.Roaming.RemoteChronologySchedulerSource
import Leanux.Proofs.WG.Roaming.RemoteDriverDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Deferred
theorem atoms (entry : RemoteMap) :
    RxHistory.DeferredSource.AtomContracts (Inv entry) RemoteDriver.Safe
      (fun {_} a => RemoteDriver.focus a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact focus_audit entry _ _ runOneSendWorkerAudit_erases RemoteDriver.Deferred.send_retained
  · exact focus_audit entry _ _ runOneClearWorkerAudit_erases RemoteDriver.Deferred.clear_retained
  · intro what queues
    exact mixed_store entry _ _ (requireDrainedPrefix_erases what queues)
      (PendingScheduler.requireDrained_store what queues)
  · exact audit_store entry _ _ getDevSavedAudit_erases (liftWG_sameProductStore _ getDev_sameWGStore)
  · intro d j; exact audit_store entry _ _ (wheelNextDueAudit_erases d j) (SameView.pure _ _)
  · intro b; exact audit_store entry _ _ (requireStepCompleteAudit_erases b) (PendingScheduler.requireStepComplete_store b)
  · intro j; exact audit_store entry _ _ (requireNothingDueAudit_erases j) (PendingScheduler.requireNothingDue_store j)
  · intro worker pid timer wheel prior
    exact focus_audit entry _ _ (timerDispatchAudit_erases worker pid timer wheel prior)
      (fun before => RemoteDriver.Deferred.timer_retained before worker pid timer wheel prior)
  · intro j
    exact focus_audit entry _ _ (RxHistory.placeholderTimerPass_erases j)
      (fun before => RemoteDriver.Deferred.placeholder_retained before j)
  · exact mixed_store entry _ _ requireIdleDevicePrefix_erases PendingScheduler.requireIdleDevice_store
  · exact audit_store entry _ _ (erasesPrefix_lift _) requireNoCryptWork_sameKernel
  · intro timer; exact audit_store entry _ _ (erasesPrefix_lift _) (timerWorker_sameKernel timer)
  · intro ticks; exact audit_store entry _ _ (advanceAudit_erases ticks) (advance_sameKernel ticks)

theorem sendOne_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.sendOne :=
  (atoms entry).sendOne

theorem crypt_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.crypt :=
  RxHistory.DeferredSource.crypt_preserves (safe entry) (store_inv entry) _
    (Scheduler.schedule_preserves entry none)

theorem send_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.send :=
  RxHistory.DeferredSource.send_preserves (safe entry) (store_inv entry) _ (atoms entry) _
    (Scheduler.schedule_preserves entry none)

theorem afterXmit_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.afterXmit :=
  RxHistory.DeferredSource.afterXmit_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) _ (send_preserves entry)

theorem timers_preserves (entry : RemoteMap) (j : UInt64) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Deferred.timers j) :=
  RxHistory.DeferredSource.timers_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) j

theorem placeholder_preserves (entry : RemoteMap) (j : UInt64) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Deferred.placeholder j) :=
  RxHistory.DeferredSource.placeholder_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) _ (send_preserves entry) j

theorem idle_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.idle :=
  RxHistory.DeferredSource.idle_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (timers_preserves entry) _ (placeholder_preserves entry)

theorem afterAdvance_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Deferred.afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (timers_preserves entry) _ (placeholder_preserves entry)

theorem deferred_preserves (entry : RemoteMap) (call : EnvDeferredCall) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Deferred.deferred call) :=
  RxHistory.DeferredSource.deferred_preserves _ (atoms entry) _ _ _ _ _ _ _
    (crypt_preserves entry) (send_preserves entry) (afterXmit_preserves entry)
    (timers_preserves entry) (placeholder_preserves entry)
    (idle_preserves entry) (afterAdvance_preserves entry) call
end Deferred

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
