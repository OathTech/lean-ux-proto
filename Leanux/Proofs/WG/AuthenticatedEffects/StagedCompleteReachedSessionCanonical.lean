import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical

/-! Session allocation, derivation and rotation expose their actual accesses and saved-peer metadata writes. No TX ownership is changed by these operations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def keyCreateShape (peer : Option PeerId) : Shape (keypairCreate peer) := by
  unfold keypairCreate setKeypair
  repeat' first
    | (metadata_source_head modify; apply Shape.access; apply Access.Shape.write; exact KeyFrames.world _ (fun _=>rfl))
    | metadata_source_step

noncomputable def deriveShape (kp : KeypairId) (initiator : Bool) (key : Key) : Shape (deriveKeys kp initiator key) := by
  unfold deriveKeys setKeypair
  repeat' metadata_source_step

noncomputable def zeroShape (pid : PeerId) : Shape (handshakeZero pid) := by
  unfold handshakeZero
  repeat' metadata_source_step

noncomputable def rotateShape (pid : PeerId) (kp : KeypairId) : Shape (addNewKeypair pid kp) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (metadata_source_head keypairPut; exact .access (Access.putShape _ _))
    | metadata_source_step

noncomputable def sessionShape (pid : PeerId) : Shape (beginSession pid) := by
  unfold beginSession
  repeat' first
    | (metadata_source_head keypairCreate; exact keyCreateShape _)
    | (metadata_source_head deriveKeys; exact deriveShape _ _ _)
    | (metadata_source_head handshakeZero; exact zeroShape _)
    | (metadata_source_head addNewKeypair; exact rotateShape _ _)
    | unfold setKeypair
    | metadata_source_step

noncomputable def initiationShape (pid : PeerId) : Shape (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  repeat' metadata_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
