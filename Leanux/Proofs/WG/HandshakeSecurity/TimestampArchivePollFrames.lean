import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveReceive

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem counter (kid : KeypairId) (nonce : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' archive_traffic_step history

theorem drop_rx (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  repeat' archive_traffic_step history

macro "archive_poll_step " history:term : tactic => `(tactic| first
  | (rx_retention_head counterValidate; exact counter _ _ $history)
  | (rx_retention_head dropRxQueue; exact drop_rx _ $history)
  | (rx_retention_head PrevQueue.peek; exact frame_store $history _ (prevQueuePeek_sameWGStore _))
  | (rx_retention_head endpointFromSkb; exact frame_store $history _ (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; exact skb _ $history)
  | (rx_retention_head freeRxSkb; exact skb _ $history)
  | archive_receive_step $history)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
