import PairLookupFields

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

theorem chain_head_bound {n o m b previous nodes} (shape : Chain n o m b previous nodes)
    (layout : Layout o) (storage : storageCheck n o=true) : head nodes<2^64 := by
  cases shape with
  | nil => decide
  | @cons previous link entry rest fields tail =>
    have bound := entry_bound storage fields.named
    have valid := fields.valid
    simp only [layout.hash,layout.entrySize] at bound valid
    change link<2^64
    omega

/-- The old loop predicate is a consequence of the executable all-bucket
decoder. Backlinks and other buckets remain in the shared relation. -/
theorem chain_physical {n o m b previous nodes} (shape : Chain n o m b previous nodes)
    (layout : Layout o) (storage : storageCheck n o=true)
    (names : interpretationCheck n=true) :
    BucketShape m (.ofNat 64 (head nodes))
      (nodes.map fun (_,entry) => (physicalOwner n entry.owner,entry)) := by
  induction shape with
  | nil => rfl
  | @cons previous link entry rest fields tail ih =>
    have interpreted := interpretation_owner names fields.named
    have linkBound := chain_head_bound (Chain.cons fields tail) layout storage
    change link<2^64 at linkBound
    have addr : BitVec.ofNat 64 link=physicalOwner n entry.owner+8 := by
      rw [interpreted.1]
      change BitVec.ofNat 64 link=BitVec.ofNat 64 (link-o.hash)+8#64
      rw [←BitVec.ofNat_add]
      congr 1
      have valid := fields.valid
      rw [layout.hash] at valid ⊢
      omega
    have nonzero : BitVec.ofNat 64 link≠0 := by
      intro zero
      have raw := congrArg BitVec.toNat zero
      have nonzero := fields.nonzero
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt linkBound] at raw
      exact nonzero raw
    refine ⟨interpreted.2,nonzero,addr,word_bound fields.index,?_,?_,.ofNat 64 (head rest),?_,ih⟩
    · have read := word_loadInt _ _ _ _ _ fields.kind
      rw [interpreted.1]
      simp only [layout.kind,BitVec.ofNat_add,Layouts.entry_type] at read ⊢
      cases entry with | mk index owner => cases owner <;> exact read
    · have read := word_loadInt _ _ _ _ _ fields.index
      change m.loadInt (physicalOwner n entry.owner+.ofNat 64 Layouts.entry_index) 4=some (entry.index : Int)
      rw [interpreted.1]
      simpa only [layout.index,BitVec.ofNat_add,Layouts.entry_index] using read
    · have read := word_loadInt _ _ _ _ _ fields.forward
      change m.loadInt (BitVec.ofNat 64 link+0#64) 8=some ((BitVec.ofNat 64 (head rest)).toNat : Int)
      rw [BitVec.add_zero,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (chain_head_bound tail layout storage)]
      simpa only [layout.next,Nat.add_zero] using read

theorem bucket_physical {n o m d query} (related : Corresponds n o m d)
    (storage : storageCheck n o=true) (names : interpretationCheck n=true) :
    ∃ first : BitVec 64,
      m.loadInt (BitVec.ofNat 64 n.table+.ofNat 64 (8*(query%8192))) 8=some (first.toNat : Int) ∧
      BucketShape m first ((d.indexTable.filter (fun e => e.index%8192==query%8192)).map
        fun e => (physicalOwner n e.owner,e)) := by
  have layout := (validate_basic (reconstruct_components related).1).1
  have decoded := reconstruct_bucket related (b := query%8192) (Nat.mod_lt _ (by decide))
  obtain ⟨first,read,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,_,_,_⟩ := bucket_shape run
  refine ⟨.ofNat 64 first,?_,?_⟩
  · have raw := word_loadInt _ _ _ _ _ read
    simpa only [tableHead,layout.buckets,layout.headSize,layout.first,Nat.add_zero,
      Nat.mul_comm,BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (word_bound read)] using raw
  · rw [headEq,entriesEq,List.map_map]
    exact chain_physical shape layout storage names

#print axioms bucket_physical
end Binary.Pair.IndexLookup
