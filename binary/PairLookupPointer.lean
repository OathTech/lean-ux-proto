import PairLookupFields

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

theorem find_address {pairs : List (Nat×Nat)} {id base : Nat}
    (unique : (pairs.map Prod.snd).Nodup) (member : (id,base) ∈ pairs) :
    pairs.find? (·.2==base)=some (id,base) := by
  induction pairs with
  | nil => cases member
  | cons pair pairs ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : pair.2≠base := by
        intro same
        exact parts.1 (same ▸ List.mem_map.mpr ⟨(id,base),member,rfl⟩)
      simpa only [List.find?_cons,show (pair.2==base)=false from beq_eq_false_iff_ne.mpr different] using ih parts.2 member

theorem peerId_pointer {n o} (validation : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (names : interpretationCheck n=true) (path : String) (value : Option PeerId)
    (named : ∀ pid, value=some pid → ∃ base, (pid,base) ∈ n.peers) :
    peerId n path (OwnerWord.pointer (peerPointer n) value).toNat=.ok value := by
  cases value with
  | none => rfl
  | some pid =>
    obtain ⟨base,member⟩ := named pid rfl
    have fields := validate_basic validation
    have bound := (storage_bounds storage (count_storage member)).2
    rw [fields.1.peerRefcount] at bound
    have bounded : base<2^64 := by
      have : 0<Layouts.peer_refcount+4 := by decide
      dsimp only at bound
      omega
    have positive := interpretation_peer names member
    rw [peerPointer,Trie.interpretation_of_mem fields.2.2.2.1 member] at positive
    have nonzero : base≠0 := by intro zero; rw [zero] at positive; exact positive rfl
    simp only [OwnerWord.pointer,peerPointer,Trie.interpretation_of_mem fields.2.2.2.1 member,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded,peerId,beq_iff_eq,nonzero,↓reduceIte,
      find_address fields.2.2.2.2 member]
    rfl

theorem field_decode {n o m owner base value} (validation : n.validate o=.ok ())
    (storage : storageCheck n o=true) (names : interpretationCheck n=true)
    (ownerNamed : (owner,base) ∈ n.owners)
    (valueNamed : ∀ pid, value=some pid → ∃ address, (pid,address) ∈ n.peers)
    (field : OwnerWord.Field (peerPointer n) m (physicalOwner n owner) value) :
    (do
      let path := s!"owner[{repr owner}].peer"
      let raw ← word m path (base+o.peer) 8
      return (owner,←peerId n path raw))=.ok (owner,value) := by
  have layout := (validate_basic validation).1
  have bound := entry_bound storage ownerNamed
  rw [layout.entrySize] at bound
  have read := field
  unfold OwnerWord.Field at read
  rw [(interpretation_owner names ownerNamed).1] at read
  have wordRead := Trie.word_of_loadInt s!"owner[{repr owner}].peer" (by omega : base+8≤2^64) read
  simp only [layout.peer,Nat.add_zero,wordRead]
  change (do
    let peer ← peerId n s!"owner[{repr owner}].peer" (OwnerWord.pointer (peerPointer n) value).toNat
    pure (owner,peer))=.ok (owner,value)
  rw [peerId_pointer validation storage names _ value valueNamed]
  rfl

#print axioms field_decode
end Binary.Pair.IndexLookup
