import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- Combine the landed next-slot and allocation-material frames; endpoint
updates neither install nor consume a pending allocation identity. -/
theorem setPeerEndpoint_frame (pid : PeerId) (endpoint : Endpoint) :
    SameView view (setPeerEndpoint pid endpoint) :=
  frame_from_fields
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) pid endpoint)
    (Keypairs.WGFrames.setPeerEndpoint_sameSnapshot pid endpoint)

end Leanux.Proofs.WG.Noise.PendingTickets
