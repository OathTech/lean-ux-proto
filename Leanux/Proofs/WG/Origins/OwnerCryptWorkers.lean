import Leanux.Proofs.WG.Origins.OwnerWorkers
import Leanux.Proofs.WG.Origins.OwnerPrepare

/-! Actual decrypt-worker iterations compose the same committed journal used
by polling, prepare and payment. Source failures retain their recorded prefix. -/
namespace Leanux.Proofs.WG.OwnerCryptWorkers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
open Origins.HistorySupport (sensitive)

private theorem pay (pid : PeerId) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) := by
  apply OwnerChecks.native_quiet _ (peerPut (some pid)) (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _)))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.pay) pid)
    (RxHistory.mixed_preserves (allocationAmbient.peerPut _).liftWGObserver.preserves)
  intro history
  exact hoare_consequence (OwnerConsume.peerPut_preserves (some pid))
    (fun _ hi => hi.2) (fun _ _ hi => hi)

theorem decryptStep : OwnerChecks.Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind OwnerWorkers.napiSoftirq
  intro _
  apply PrefixPreserves.bind OwnerPrepare.prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.safe) false
  | some pid =>
    exact OwnerWorkers.napiIrqExit.bind (fun _ => (pay pid).bind (fun _ =>
      OwnerWorkers.napiSoftirq.bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) true)))

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    OwnerChecks.Preserves (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) OwnerWorkers.store frame

theorem decryptIteration : OwnerChecks.Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) decryptStep
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  exact lift_store _ (by
    intro initial
    exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

end Leanux.Proofs.WG.OwnerCryptWorkers
