import Leanux.Proofs.WG.TransmitSecurity.NonceLifecycleFrames
import Leanux.Proofs.WG.RetirementSecurity.MaterialFrames

/-! Native session derivation and publication preserve allocation non-reuse.
The global identity step is the actual keypairCreate; material updates retain
both the identity and the already allocated sending counter. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem reference_frame {α : Type} {a : WG.M α}
    (frame : SameView RetirementSecurity.referenceNonceView a) : SameView view a :=
  frame.of_factor
    (fun s => View.mk s.1 (fun id => (s.2 id).map fun c => Cell.mk c.1 c.2.1))
    view (fun w => by
      apply View.ext
      · rfl
      · funext id
        simp only [view,RetirementSecurity.referenceNonceView,
          RetirementSecurity.referenceNonceFields,RetirementSecurity.keyAt,
          Option.map_map,Function.comp_def]
        rfl)

theorem derive (id : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView view (deriveKeys id initiator ck) :=
  reference_frame (RetirementSecurity.deriveKeys_referenceNonce id initiator ck)

theorem init_key (id : KeypairId) (initiator : Bool) (remote : Nat) :
    SameView view (SessionOrigin.initKey id initiator remote) :=
  reference_frame (RetirementSecurity.initKey_referenceNonce id initiator remote)

theorem expire (pid : PeerId) : SameView view (expireCurrentPeerKeypairs pid) :=
  reference_frame (RetirementSecurity.expire_referenceNonce pid)

theorem zero_handshake (pid : PeerId) : SameView view (handshakeZero pid) :=
  reference_frame (RetirementSecurity.full_keys_frontier_frame _
    (Origins.Retaining.handshakeZero_material pid)
    (Keypairs.WGFrames.handshakeZero_sameSnapshot pid))

theorem begin_session (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (beginSession pid) := by
  rw [SessionOrigin.factor]
  unfold SessionOrigin.front SessionOrigin.frontWith SessionOrigin.tail SessionOrigin.tailWith
  simp only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact create_preserves _ h)
    | (rx_retention_head SessionOrigin.initKey; exact native_frame h (init_key _ _ _))
    | (rx_retention_head deriveKeys; exact native_frame h (derive _ _ _))
    | (rx_retention_head handshakeZero; exact native_frame h (zero_handshake _))
    | (rx_retention_head addNewKeypair; exact rotate _ _ h)
    | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
    | (rx_retention_head liftIndex; exact native_frame h (index _))
    | nonce_preserves_step h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
