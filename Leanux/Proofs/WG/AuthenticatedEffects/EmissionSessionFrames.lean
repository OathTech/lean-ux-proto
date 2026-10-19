import Leanux.Proofs.WG.AuthenticatedEffects.EmissionCompletionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingSource

/-! Native selection, allocation, derivation and role-slot updates preserve the
sent projection. These are endpoint frames for the explicit source actors;
actual socket append and stopped-prefix coverage remain separate contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem keypair_get (key : Option KeypairId) : SameView WGWorld.sent (keypairGet key) := by
  sent_frame [keypairGet,refcountIncNotZero] using [getKeypair_sent_spec,setKeypair_sent_spec]

theorem keypair_get_spec (P : List SentDatagram → Prop) (key : Option KeypairId) :
    Preserves (fun w => P w.sent) (keypairGet key) := (keypair_get key).wp P

theorem selection (pid : PeerId) : SameView WGWorld.sent (HandshakeSecurity.Responder.selectionPrefix pid) := by
  sent_frame [HandshakeSecurity.Responder.selectionPrefix]
    using [getPeer_sent_spec,setPeer_sent_spec,keypair_get_spec]

theorem keypair_create (owner : Option PeerId) : SameView WGWorld.sent (keypairCreate owner) := by
  sent_frame [keypairCreate,hiddenAlloc] using [setKeypair_sent_spec]

theorem keypair_create_spec (P : List SentDatagram → Prop) (owner : Option PeerId) :
    Preserves (fun w => P w.sent) (keypairCreate owner) := (keypair_create owner).wp P

theorem add_keypair (pid : PeerId) (key : KeypairId) : SameView WGWorld.sent (addNewKeypair pid key) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec,getKeypair_sent_spec,keypair_put_spec]

theorem confirmed (pid : PeerId) (key : KeypairId) : SameView WGWorld.sent (receivedWithKeypair pid key) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec,keypair_put_spec]

theorem derived (key : KeypairId) (initiator : Bool) (chaining : Key) :
    SameView WGWorld.sent (deriveKeys key initiator chaining) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold deriveKeys
  simp only [hiddenClock64]
  repeat' consumer_sent_step initial

theorem session (pid : PeerId) : SameView WGWorld.sent (beginSession pid) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold beginSession WG.andM
  simp only [branch,invariant,unsupported,IndexOwner.peerWord,IndexOwner.peerDeref,handshakeZero]
  repeat' first
    | (cookie_source_head keypairCreate; exact keypair_create_spec (fun s => s = initial) _)
    | (cookie_source_head deriveKeys; exact (derived _ _ _).wp (fun s => s = initial))
    | (cookie_source_head addNewKeypair; exact (add_keypair _ _).wp (fun s => s = initial))
    | consumer_sent_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
