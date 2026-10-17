import Leanux.Proofs.WG.Packets.PublicationJoint
import Leanux.Proofs.WG.Packets.PublicationFrontierPrepare
import Leanux.Proofs.WG.Origins.OwnerCryptWorkers

/-! Concrete poll, NAPI and decrypt-worker calls preserve owner evidence and
positional packet certificates on the unchanged receive observer. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem poll (pid : PeerId) (budget : Nat) : Preserves (RxHistory.observePoll pid budget) :=
  combine _ (OwnerWorkers.poll pid budget) (PublicationChecks.actual_poll pid budget)

private theorem pending : Preserves (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply native_mixed _ RxNapi.pendingSource
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerWorkers.«0».Leanux.Proofs.WG.OwnerWorkers.pending)
    RxNapi.pending_erases
  intro history
  unfold RxNapi.pendingSource
  exact preserves_bind (PublicationFrontier.store_preserves getDev_sameWGStore history)
    (fun _ => preserves_pure _)

private theorem scheduled : Preserves (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply native_mixed _ RxNapi.scheduledSource
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerWorkers.«0».Leanux.Proofs.WG.OwnerWorkers.scheduled)
    RxNapi.scheduled_erases
  intro history
  unfold RxNapi.scheduledSource
  exact preserves_bind (PublicationFrontier.store_preserves getDev_sameWGStore history)
    (fun _ => preserves_pure _)

theorem napiSoftirq : Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.safe) store pending poll

theorem pollScheduledInline : Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ hi => hi.safe) store pending poll

theorem napiIrqExit : Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.safe) store scheduled napiSoftirq

/-- Actual prepare supplies the new publication anchor and owner bound.
It appends no consumed event, so old consume certificates keep their positions. -/
theorem prepare : Preserves Origins.HistoryAdapters.prepare := by
  have frame : HistoryFrame PublicationChecks.sensitive Origins.HistoryAdapters.prepare :=
    Origins.HistoryAdapters.focus_other PublicationChecks.sensitive
      (by intro event; cases event <;> rfl) _
  intro w h hi
  obtain ⟨suffix,appends,ownerSafe,post⟩ :=
    PublicationFrontier.prepare_preserves w h ⟨hi.1,hi.2.1⟩
  have certificates := PublicationChecks.Safe.of_unchanged (w := w) Origins.HistoryAdapters.prepare
    (Appends.focus _ _ _) frame hi.2.2
  refine ⟨suffix,appends,⟨ownerSafe,certificates⟩,?_⟩
  cases result : (runPrefix Origins.HistoryAdapters.prepare w h).1 with
  | error stop => trivial
  | ok out =>
    simp only [result] at post ⊢
    exact ⟨post.1,post.2,certificates⟩

private theorem pay (pid : PeerId) :
    Preserves (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) :=
  native_mixed _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCryptWorkers.«0».Leanux.Proofs.WG.OwnerCryptWorkers.pay) pid)
    (peerPutMixed_erases _) (PublicationFrontier.peerPut_preserves (some pid))

theorem decryptStep : Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind napiSoftirq
  intro _
  apply PrefixPreserves.bind prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.safe) false
  | some pid =>
    exact napiIrqExit.bind (fun _ => (pay pid).bind (fun _ =>
      napiSoftirq.bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) true)))

theorem decryptIteration : Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) decryptStep
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  exact lift_store _ (by
    intro initial
    exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

end Leanux.Proofs.WG.PublicationJoint
