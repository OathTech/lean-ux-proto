import PairIndexAssert
import SequentialRelation

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

def ownerPointer (n : Names) (owner : IndexOwner) : BitVec 64 :=
  .ofNat 64 (((n.owners.find? (·.1==owner)).map Prod.snd).getD 0)

def peerPointer (n : Names) : PeerId → BitVec 64 := Trie.interpretation n.peers
def keypairPointer (n : Names) (id : KeypairId) : BitVec 64 := ownerPointer n (.keypair id)
def physicalOwner (n : Names) : IndexOwner → BitVec 64 :=
  OwnerWord.address (peerPointer n) (keypairPointer n)

/-- Immutable interpretation compatibility with the reused compiled-image
lemmas. No peer word, count, membership or source history is constrained. -/
def interpretationCheck (n : Names) : Bool :=
  n.owners.all (fun (owner,base) => physicalOwner n owner==BitVec.ofNat 64 base &&
    physicalOwner n owner != 0) &&
  n.peers.all (fun (id,_) => peerPointer n id != 0)

theorem interpretation_owner {n owner base} (checked : interpretationCheck n=true)
    (named : (owner,base) ∈ n.owners) : physicalOwner n owner=.ofNat 64 base ∧ physicalOwner n owner≠0 := by
  have parts : n.owners.all (fun (owner,base) => physicalOwner n owner==BitVec.ofNat 64 base && physicalOwner n owner != 0)=true ∧ n.peers.all (fun (id,_) => peerPointer n id != 0)=true := by
    simpa only [interpretationCheck,Bool.and_eq_true] using checked
  have all := parts.1
  simpa only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne] using List.all_eq_true.mp all (owner,base) named

theorem interpretation_peer {n id base} (checked : interpretationCheck n=true)
    (named : (id,base) ∈ n.peers) : peerPointer n id≠0 := by
  have parts : n.owners.all (fun (owner,base) => physicalOwner n owner==BitVec.ofNat 64 base && physicalOwner n owner != 0)=true ∧ n.peers.all (fun (id,_) => peerPointer n id != 0)=true := by
    simpa only [interpretationCheck,Bool.and_eq_true] using checked
  simpa only [bne_iff_ne] using List.all_eq_true.mp parts.2 (id,base) named

def callConfig (n : Names) (w : World) (d : Device) (query : Nat) (kinds : List IndexKind) : LookupRelation.Config :=
  let bucket := d.indexTable.filter (fun e => e.index%8192==query%8192)
  let selected := (bucket.find? (fun e => e.index==query)).bind fun e =>
    if kinds.contains e.kind then some e.owner else none
  ⟨.ofNat 64 n.table,query,kinds,peerPointer n,keypairPointer n,
    ⟨selected,selected.bind fun owner => (OwnerWord.value d owner).join⟩,w.steps.toList,w.netRxSection⟩

def callView (c : LookupRelation.Config) (d : Device) : LookupRelation.View :=
  ⟨d.indexTable.filter (fun e => e.index%8192==c.query%8192),
    c.focus.owner.bind (OwnerWord.value d),c.focus.peer.bind (fun id => (d.peers.get? id).map (·.refcount))⟩

theorem callConfig_owner (n w d query kinds owner) :
    LookupRelation.ownerAddress (callConfig n w d query kinds) owner=physicalOwner n owner := rfl

theorem peerId_value {n : Names} {path : String} {raw : Nat} {id : Option PeerId}
    (unique : (n.peers.map Prod.fst).Nodup) (bounded : raw<2^64)
    (read : peerId n path raw=.ok id) :
    (OwnerWord.pointer (peerPointer n) id).toNat=raw ∧
      (∀ pid, id=some pid → peerPointer n pid≠0) := by
  have converted : Trie.pointer n.peers path raw=.ok id := by
    unfold peerId at read
    unfold Trie.pointer
    split at read
    · rename_i zero
      rw [ite_eq_left zero]
      exact read
    · rename_i nonzero
      rw [ite_eq_right nonzero]
      cases found : n.peers.find? (·.2==raw) with
      | none => rw [found] at read; cases read
      | some pair => rw [found] at read; cases pair; exact read
  have value := Trie.pointer_value unique bounded converted
  cases id <;> exact value

#print axioms peerId_value
end Binary.Pair.IndexLookup
