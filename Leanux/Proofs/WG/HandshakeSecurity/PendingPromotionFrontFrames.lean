import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionPoll
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverFrontFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Packets

/-- C2 native destination and staged-queue frames at
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`. The facts preserve only the
pending allocation projection, independently of any confirmation history. -/
structure H1PendingStackFrames : Prop where
  /-- `Noise.PendingStack.lookupDst_frame`. -/
  lookup : ∀ family addr, SameView PendingPromotion.view (lookupDst family addr)
  /-- `Noise.PendingStack.xmitTrim_pending_variant`. -/
  trim : ∀ pid, SameView PendingPromotion.view (xmitTrim pid)
  /-- `Noise.PendingStack.xmitSplice_pending_variant`. -/
  splice : ∀ pid packets, SameView PendingPromotion.view (xmitSplice pid packets)

namespace PendingPromotion
open Leanux.Proofs.Logged Queues TransmitSecurity

theorem Carrier.tx_front (frames : H1PendingStackFrames) (family addr : Nat)
    (packets : List WG.Packet) (mtu : Nat) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (txFront family addr packets mtu) := by
  unfold txFront txCheck txSelect txError txHeaders txWalk WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst
       exact Carrier.from_frame (Responder.DriverCuts.carrier_lookup _ _) (frames.lookup _ _) confirmed)
    | (rx_retention_head xmitTrim
       exact Carrier.from_frame (Responder.DriverCuts.carrier_trim _) (frames.trim _) confirmed)
    | (rx_retention_head xmitSplice
       exact Carrier.from_frame (Responder.DriverCuts.carrier_splice _ _) (frames.splice _ _) confirmed)
    | (rx_retention_head loopbackSend; exact Carrier.store confirmed (loopbackSend_kernel _ _))
    | (allocation_release_lift_from Net.M; exact Carrier.store confirmed (liftRouting_sameWGStore _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Preserves (Carrier confirmed) _)
    | pending_carrier_poll_step (), confirmed

end PendingPromotion
end Leanux.Proofs.WG.HandshakeSecurity
