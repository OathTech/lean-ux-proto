import Leanux.Proofs.WG.Index.CreatorSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Legacy statement unchanged, instantiated from the one creator traversal. -/
theorem createInitiation_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid) (View.HandshakePublisherSafe pid)
      (fun _ => View.HandshakePublisherSafe pid) := by
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HandshakePublisher pid d
  apply createInitiation_preserves_source pid P
  · intro ck hash
    exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · intro secret
    exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · unfold creatorPublish
    exact ensures_bind _ _
      ((ensures_iff _ _ _).mpr (Leanux.Proofs.Framing.indexOwner_peerDeref_preserves (.handshake pid) P))
      (fun _ => indexInsert_handshakePublisher pid)

/-- Legacy statement unchanged, instantiated from the one creator traversal. -/
theorem createResponse_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (createResponse pid) (View.HandshakePublisherSafe pid)
      (fun _ => View.HandshakePublisherSafe pid) := by
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HandshakePublisher pid d
  apply createResponse_preserves_source pid P
  · intro ck hash
    exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · intro secret
    exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · exact modifyPeer_handshakePublisher pid _ (fun _ => rfl) (fun _ => rfl)
  · unfold creatorPublish
    exact ensures_bind _ _
      ((ensures_iff _ _ _).mpr (Leanux.Proofs.Framing.indexOwner_peerDeref_preserves (.handshake pid) P))
      (fun _ => indexInsert_handshakePublisher pid)

end Leanux.Proofs.WG.Index
