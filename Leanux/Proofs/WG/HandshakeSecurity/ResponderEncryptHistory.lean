import Leanux.Proofs.WG.HandshakeSecurity.ResponderEncryptFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem encryptPoll : Preserves (RxHistory.mixed (liftWGObserver (liftWGPrefix TxRing.pollSource))) :=
  native_mixed _ _ (erasesStatePrefix_lift _) encryptPoll_native

theorem encryptTail (item : Option (List SkbId)) : Preserves (RxHistory.mixed (RxWorkers.encryptTail item)) :=
  mixed _ _ (RxWorkers.encryptTail_erases item) (encryptTail_native item)

theorem encryptIteration (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact encryptPoll.bind (fun item => (napiSoftirq H1 slots).bind (fun _ => encryptTail item))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
