import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutingCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerAcquireFrames

/-! The receive helper adapters have fixed source trees. Trie and index
computations act on their own state; their WG reads and writes stay explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def deviceReadShape : Shape getDev := by
  repeat' metadata_source_step

noncomputable def dereferenceShape (owner : IndexOwner) : Shape owner.peerDeref := by
  repeat' receive_metadata_step

noncomputable def endianShape (bits : Nat) : Shape (swapEndian bits) := by
  unfold swapEndian
  repeat' receive_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
