import Leanux.Proofs.WG.Index.ReachedDeferredAtomsSource
import Leanux.Proofs.WG.Index.DeferredSavedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedDeferred
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem crypt (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (ReachedScheduler.schedule_preserves initial loans before none)

theorem sendAll (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor,←DriverTags.Deferred.send_source]
  exact DriverTags.Deferred.send_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (hooks initial loans before) _ (ReachedScheduler.schedule_preserves initial loans before none)

theorem afterXmit (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact DriverTags.Deferred.afterXmit_preserves_drained (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (drained initial loans before) _ _ (crypt initial loans before) (sendAll initial loans before)

theorem timers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (j : UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.runTimers j) :=
  DeferredRules.runTimers_preserves_saved_variant (I:=Reached.Aux initial loans before) (S:=OwnerChecks.Safe)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre)
    (saved_spec initial loans before) (wheel_spec initial loans before)
    (timerDispatch initial loans before) (stepComplete initial loans before)
    (ReachedWorkers.send_observed initial loans before) (ReachedWorkers.clear_observed initial loans before)
    (crypt initial loans before) j

theorem placeholder (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (j : UInt64) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor,←DriverTags.Deferred.placeholder_source]
  exact DriverTags.Deferred.placeholder_preserves_saved (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (saved initial loans before) _ (hooks initial loans before) _ _
    (crypt initial loans before) (sendAll initial loans before) j

theorem idle (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact DriverTags.Deferred.idle_preserves_nothingDue (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (nothingDue initial loans before) _ _ (timers initial loans before) (placeholder initial loans before)

theorem afterAdvance (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact DriverTags.Deferred.afterAdvance_preserves_nothingDue (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe) (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (nothingDue initial loans before) _ _ (timers initial loans before) (placeholder initial loans before)

theorem stored_call (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (call : EnvDeferredCall) (frame : SameProductStore call.original) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.deferred call) :=
  ReachedScheduler.observed_store initial loans before _ _
    (HolderAuxTimers.deferred initial loans before call) (RxHistory.deferred_erases call) frame

theorem deferred (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (call : EnvDeferredCall) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact drained initial loans before what queues
  | idleDevice => exact stored_call initial loans before _ PendingScheduler.requireIdleDevice_store
  | noCrypt => exact stored_call initial loans before _ requireNoCryptWork_sameKernel
  | crypt => exact crypt initial loans before
  | sendOne => exact ReachedWorkers.send_observed initial loans before
  | clearOne => exact ReachedWorkers.clear_observed initial loans before
  | sendAll => exact sendAll initial loans before
  | afterXmit => exact afterXmit initial loans before
  | timerWorker timer => exact stored_call initial loans before _ (timerWorker_sameKernel timer)
  | timers j => exact timers initial loans before j
  | placeholder j => exact placeholder initial loans before j
  | idle => exact idle initial loans before
  | advance ticks => exact stored_call initial loans before _ (advance_sameKernel ticks)
  | afterAdvance => exact afterAdvance initial loans before

end Leanux.Proofs.WG.Index.ReachedDeferred
