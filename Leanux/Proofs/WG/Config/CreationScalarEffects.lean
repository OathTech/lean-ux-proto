import Leanux.Proofs.WG.Config.CreationScalarModel

/-! Pure scalar congruence and effective-flag facts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes
open PeerScalarRetention

theorem prefixCell_congr (p q : Peer) (psk : Option Key) (endpoint : Option EndpointAttr)
    (same : cell p=cell q) :
    ScalarTail.prefixCell p psk endpoint=ScalarTail.prefixCell q psk endpoint := by
  have fields : p.internalId=q.internalId ∧ p.presharedKey=q.presharedKey ∧
      p.persistentKeepaliveInterval=q.persistentKeepaliveInterval ∧ p.endpoint=q.endpoint := by
    simpa only [cell,Prod.mk.injEq] using same
  cases psk <;> cases endpoint
  all_goals simp only [ScalarTail.prefixCell,ScalarPrefix.effectPeer,ScalarPrefix.keyedPeer]
  all_goals first
    | (solve | simp only [cell,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2])
    | (unfold endpointAttributePeer
       split
       · simp only [cell,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2]
       · simp only [endpointStoredPeer,fields.2.2.2]
         split <;> simp only [cell,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2])

theorem initialized_cell (key : Key) (stamp : Nat) (psk : Option Key) :
    cell (initializedPeer key stamp psk)=initCell psk (newbornCell stamp) := rfl

theorem masked_remove (flags : UInt32) :
    (flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS) &&& WGPEER_F_REMOVE_ME=
      flags &&& WGPEER_F_REMOVE_ME := by
  apply UInt32.eq_of_toBitVec_eq
  change (flags.toBitVec &&& ~~~(2 : BitVec 32)) &&& (1 : BitVec 32)=flags.toBitVec &&& 1
  rw [BitVec.and_assoc]
  rfl

end Leanux.Proofs.WG.Config.CreationScalar
