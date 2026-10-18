import Leanux.Proofs.WG.Noise.PendingTicketAllowedIpFrames
import Leanux.Proofs.WG.Noise.PendingTicketFlushFrames
import Leanux.Proofs.WG.Index.BulkRemovalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

theorem peerRemove_retained (peer : Option PeerId) : RetainsCall (peerRemove peer) := by
  apply retains_of_preserves
  intro entry
  exact Index.peerRemove_preserves _
    (fun pid => retained_preserves (retained_of_frame (peerMakeDead_frame pid)) entry)
    (fun pid => retained_preserves (peerRemoveAfterDead_retained pid) entry) peer

/-- Both saved-peer loops remove pending tickets without changing a surviving
allocation identity or resetting the global allocation frontier. -/
theorem peerRemoveAll_retained : RetainsCall peerRemoveAll := by
  apply retains_of_preserves
  intro entry
  exact Index.peerRemoveAll_preserves _
    (retained_preserves (retained_of_frame free_frame) entry)
    (fun pid => retained_preserves (retained_of_frame (peerMakeDead_frame pid)) entry)
    (fun pid => retained_preserves (peerRemoveAfterDead_retained pid) entry)

end Leanux.Proofs.WG.Noise.PendingTickets
