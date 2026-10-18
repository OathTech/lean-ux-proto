import Leanux.Proofs.WG.TransmitSecurity.NonceReceiveFrames

/-! Poll bookkeeping preserves the nonce projection. Replay acceptance updates
only receiving state; releasing the packet's key may erase a live cell. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

macro "nonce_poll_native_step " h:term : tactic => `(tactic| first
  | (rx_retention_head counterValidate; exact native_frame $h (receive_counter _ _))
  | (rx_retention_head PrevQueue.peek; exact native_frame $h (store (prevQueuePeek_sameWGStore _)))
  | (rx_retention_head endpointFromSkb; exact native_frame $h (store (endpointFromSkb_sameWGStore _)))
  | (rx_retention_head getRxSkb; exact native_frame $h (skb _))
  | (rx_retention_head freeRxSkb; exact native_frame $h (skb _))
  | (rx_retention_head liftSkb; exact native_frame $h (skb _))
  | nonce_preserves_step $h)

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
