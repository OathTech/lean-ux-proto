import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionQuiet

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

/-- Local pending-slot frames from C2 H1 at
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`.

The observation is the same `Noise.PendingTickets.view`, expanded through
`PendingTickets.view_slot`. Each field below cites its native declaration.
These are ordinary single-call projected effects, with no execution history,
confirmation list, initialized invariant, or uniqueness conclusion assumed. -/
structure H1PendingQuietFrames : Prop where
  /-- `Noise.PendingTickets.sendStagedPackets_retained`. -/
  staging : ∀ pid, ProjectedAction PendingPromotion.view Retained (sendStagedPackets pid)
  /-- `Noise.PendingTickets.sendKeepalive_retained`. -/
  keepalive : ∀ pid, ProjectedAction PendingPromotion.view Retained (sendKeepalive pid)
  /-- `Noise.PendingTickets.setPeerEndpoint_frame`. -/
  endpoint : ∀ pid ep, SameView PendingPromotion.view (setPeerEndpoint pid ep)
  /-- `Noise.PendingTickets.afterConfirmation_retained`; the native
  `ConsumeConfirmation.afterConfirmation` body is identical to C3's factor. -/
  receiveTail : ∀ pid pkt confirmed, ProjectedAction PendingPromotion.view Retained
    (Confirmation.afterConfirmation pid pkt confirmed)

end Leanux.Proofs.WG.HandshakeSecurity
