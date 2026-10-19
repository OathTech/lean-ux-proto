import Leanux.Proofs.WG.Config.GetterScalarModel
import Leanux.Proofs.WG.Config.UpdateOnlyModel

/-! Deletion-aware serialized-scalar preservation outside the actual selected slot. Cells include allocation identity, PSK, interval and the getter-visible endpoint. The quiet arm allows work and deletion; the missing arm alone does not assert allocation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Other
open Leanux Leanux.WG

def ExceptAt (selected : PeerId) (before after : GetterScalar.Map) : Prop :=
  ∀ pid value, pid ≠ selected → after pid=some value → before pid=some value

def Keeps (selected : PeerId) (entry final : Campaign2.Snapshot) : Prop :=
  ExceptAt selected (GetterScalar.observation entry) (GetterScalar.observation final)

theorem accepted_fields (attrs : PeerAttrs)
    (accepted : UpdateOnly.validationError attrs=none) :
    ∃ key,attrs.publicKey=some key ∧
      attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0 ∧
      (attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1) := by
  cases pubkey : attrs.publicKey with
  | none=>simp [UpdateOnly.validationError,pubkey] at accepted
  | some key=>
    have valid:attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0:=by
      by_cases good:attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0
      · exact good
      · simp [UpdateOnly.validationError,pubkey,good] at accepted
    refine ⟨key,rfl,valid,?_⟩
    cases protocol : attrs.protocolVersion with
    | none=>exact Or.inl rfl
    | some version=>
      by_cases good:version=1
      · exact Or.inr (congrArg some good)
      · simp [UpdateOnly.validationError,pubkey,valid,protocol,good] at accepted

theorem remove_blocks (flags : UInt32) (remove : flags &&& WGPEER_F_REMOVE_ME≠0) :
    flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY)≠0 := by
  intro zero
  have masked:=congrArg (fun n : UInt32=>n &&& WGPEER_F_REMOVE_ME) zero
  have same:(flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY)) &&& WGPEER_F_REMOVE_ME=
      flags &&& WGPEER_F_REMOVE_ME:=by
    apply UInt32.eq_of_toBitVec_eq
    simp [WGPEER_F_REMOVE_ME,WGPEER_F_UPDATE_ONLY,BitVec.and_assoc]
  exact remove (same.symm.trans (by simpa using masked))

inductive CommandEffect (attrs : PeerAttrs) (before : Device)
    (after : GetterScalar.Map) : Prop
  | quiet (kept : ∀pid value,after pid=some value →
      GetterScalar.values (some before) pid=some value)
  | existing (key : Key) (pid : PeerId) (p : Peer)
      (pubkey : attrs.publicKey=some key)
      (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
      (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
      (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
      (found : before.peerHashtable.find? (·.1 == key)=some (key,pid))
      (resident : before.peers[pid]?=some p)
      (others : ExceptAt pid (GetterScalar.values (some before)) after)
  | missing (key : Key)
      (pubkey : attrs.publicKey=some key)
      (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
      (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
      (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
      (absent : before.peerHashtable.find? (·.1 == key)=none)
      (others : ExceptAt before.nextPeer (GetterScalar.values (some before)) after)

end Leanux.Proofs.WG.Config.GetterScalar.Other
