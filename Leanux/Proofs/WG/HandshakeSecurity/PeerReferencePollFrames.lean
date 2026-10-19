import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceReceive

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem counter (kid : KeypairId) (nonce : Nat) :
    Framing.Preserves Inv (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' peer_reference_traffic_step

theorem drop_rx (pid : PeerId) :
    Framing.Preserves Inv (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  repeat' peer_reference_traffic_step

macro "peer_reference_poll_step" : tactic => `(tactic| first
  | (rx_retention_head counterValidate; exact counter _ _)
  | (rx_retention_head dropRxQueue; exact drop_rx _)
  | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
  | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; exact skb _)
  | (rx_retention_head freeRxSkb; exact skb _)
  | peer_reference_receive_step)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
