import Leanux.Proofs.WG.HandshakeSecurity.ResponderDecryptFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem prepare : Preserves Origins.HistoryAdapters.prepare :=
  quiet _ _ (Appends.focus _ _ _) Origins.HistoryAdapters.prepare_erases
    (Origins.HistoryAdapters.focus_other consumer (by intro e; cases e <;> rfl) _)
    (fun confirmed => PublicationPoll.native_product _ _ (prepare_native confirmed))

theorem pay (pid : PeerId) :
    Preserves (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) :=
  native_mixed _ _ (peerPutMixed_erases _) (peerPut_native (some pid))

theorem decryptStep (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind (napiSoftirq H1 slots)
  intro _
  apply PrefixPreserves.bind prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.2) false
  | some pid =>
    exact (napiIrqExit H1 slots).bind (fun _ => (pay pid).bind (fun _ =>
      (napiSoftirq H1 slots).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) true)))

theorem decryptIteration (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (decryptStep H1 slots)
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  exact lift_store _ (by intro initial; exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
