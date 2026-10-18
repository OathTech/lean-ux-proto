import Leanux.Proofs.WG.Packets.PublicationHandshakeReceive
import Leanux.Proofs.WG.Packets.PublicationJoint

/-! The original handshake receive observer retains both owner evidence and
packet certificates on one journal, including every reached Stop prefix. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins

theorem receiveStep : Preserves HistoryAdapters.receiveStep := by
  apply quiet _ _ OwnerHandshake.receiveStep (Appends.focus _ _ _)
    HistoryAdapters.receiveStep_erases
  · exact focusPrefix_other HistoryAdapters.encode HistoryAdapters.decode
      PublicationChecks.sensitive (by intro event; cases event <;> rfl) _
  · intro history
    exact PublicationPoll.native_product _ _ (PublicationHandshake.receiveStep history)

theorem receiveIteration : Preserves HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) receiveStep
  exact lift_store _ (condResched_sameKernel .receiveWorker)

end Leanux.Proofs.WG.PublicationJoint
