import Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks

/-! Actual NAPI and decrypt-worker composition for the earlier authentication
receipts, preserving them across later internal stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

private theorem pending : Preserves (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) :=
  mixed _ (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.pending)
private theorem scheduled : Preserves (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) :=
  mixed _ (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.scheduled)

theorem napiSoftirq : Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) store pending poll

theorem pollScheduledInline : Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) store pending poll

theorem napiIrqExit : Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) store scheduled napiSoftirq

theorem prepare : Preserves Origins.HistoryAdapters.prepare :=
  quiet _ PublicationJoint.prepare (Origins.HistoryAdapters.focus_other sensitive
    (by intro event; cases event <;> rfl) _)

private theorem pay (pid : PeerId) : Preserves (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) :=
  mixed _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.pay) pid)

theorem decryptStep : Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind napiSoftirq
  intro _
  apply PrefixPreserves.bind prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.2) false
  | some pid =>
    exact napiIrqExit.bind (fun _ => (pay pid).bind (fun _ =>
      napiSoftirq.bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) true)))

theorem decryptIteration : Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) decryptStep
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  exact lift_store _ (by
    intro initial
    exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
