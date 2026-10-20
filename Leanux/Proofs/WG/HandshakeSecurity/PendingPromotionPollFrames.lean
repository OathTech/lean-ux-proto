import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionHandshake
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverPollFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

/-- Native replay-counter retention, from
`Noise.PendingSession.counter_pending` at C2 pin
`be8c209c`. No execution history is assumed. -/
structure H1PendingPollFrames : Prop where
  counter : ∀ kid nonce, SameView PendingPromotion.view (counterValidate kid nonce)

namespace PendingPromotion
open Leanux.Proofs.Logged Queues TransmitSecurity

theorem Carrier.counter (frames : H1PendingPollFrames) (kid : KeypairId) (nonce : Nat)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (counterValidate kid nonce) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_counter kid nonce) (frames.counter kid nonce) confirmed

theorem Carrier.drop (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  exact Carrier.modify_peer confirmed pid (fun p => {p with rxQueue := p.rxQueue.dropPeeked})
    (fun _ => rfl) (fun _ => rfl)

macro "pending_carrier_poll_step " frames:term "," confirmed:term : tactic => `(tactic| first
  | (receive_update_head setPeer; apply Carrier.modify_peer $confirmed; all_goals (intro p; rfl))
  | (rx_retention_head modifyDev; apply Carrier.modify_device; all_goals (intro d; rfl))
  | (rx_retention_head counterValidate; exact Carrier.counter $frames _ _ $confirmed)
  | (rx_retention_head dropRxQueue; exact Carrier.drop _ $confirmed)
  | (rx_retention_head PrevQueue.peek; exact Carrier.store $confirmed (prevQueuePeek_sameWGStore _))
  | (rx_retention_head endpointFromSkb; exact Carrier.store $confirmed (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getPeer; exact hoare_consequence (Carrier.get_peer $confirmed _) (fun _ hi => hi) (fun _ _ hi => hi.1))
  | (rx_retention_head keypairPut; exact Carrier.key_put $confirmed _ _)
  | (rx_retention_head peerPut; exact Carrier.peer_put $confirmed _)
  | (rx_retention_head getRxSkb; exact Carrier.skb $confirmed _)
  | (rx_retention_head freeRxSkb; exact Carrier.skb $confirmed _)
  | (rx_retention_head liftSkb; exact Carrier.skb $confirmed _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

end PendingPromotion
end Leanux.Proofs.WG.HandshakeSecurity
