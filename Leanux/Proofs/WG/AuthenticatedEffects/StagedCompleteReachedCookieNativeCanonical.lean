import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource

/-! The reply front and tunnel preparation expose actual native reads, guards and counter writes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def replyFrontShape (src : SkbSource) : Shape (replyFront src) := by
  unfold replyFront endpointFromSkb
  repeat' metadata_source_step

noncomputable def tunnelReplyShape (e : Endpoint) (bytes : Key) (route : Route) : Shape (tunnelReplyFront e bytes route) := by
  unfold tunnelReplyFront socketPort
  repeat' metadata_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
