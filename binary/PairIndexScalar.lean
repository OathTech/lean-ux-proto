import PairIndexSlots

namespace Binary.Pair.Index

theorem entry_address_ne {n o owner base other otherBase offset otherOffset}
    (storage : storageCheck n o=true) (named : (owner,base) ∈ n.owners)
    (otherNamed : (other,otherBase) ∈ n.owners)
    (within : offset<o.entrySize) (otherWithin : otherOffset<o.entrySize)
    (different : base=otherBase → offset≠otherOffset) : base+offset≠otherBase+otherOffset := by
  by_cases same : base=otherBase
  · have := different same
    omega
  · have separate := storage_apart storage (entry_storage named) (entry_storage otherNamed) (by
      intro equal
      exact same (congrArg Prod.fst equal))
    rcases separate with first | second <;> omega

theorem count_index_ne {n o id countBase owner base} (layout : Layout o)
    (storage : storageCheck n o=true) (count : (id,countBase) ∈ n.peers)
    (named : (owner,base) ∈ n.owners) : countBase+o.peerRefcount≠base+28 := by
  have separate := storage_apart storage (count_storage count) (entry_storage named) (by
    intro equal
    have sizes := congrArg Prod.snd equal
    rw [layout.entrySize] at sizes
    omega)
  rw [layout.entrySize] at separate
  rcases separate with first | second <;> omega

theorem DataSlot.disjoint_index {n o address size newOwner base}
    (slot : DataSlot n o address size) (layout : Layout o)
    (storage : storageCheck n o=true) (named : (newOwner,base) ∈ n.owners)
    (different : address≠base+28) :
    ∀ a, InRange (.ofNat 64 address) size a → ¬InRange (.ofNat 64 (base+28)) 4 a := by
  cases slot with
  | entry owner old offset size oldNamed field =>
    apply entry_fields_apart storage oldNamed named
    · rw [layout.entrySize]
      rcases field with h | h | h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> decide
    · rw [layout.entrySize]; decide
    · intro equal
      rcases field with h | h | h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> omega
  | count id old oldNamed =>
    apply storage_slices_apart storage (count_storage oldNamed) (entry_storage named)
    · exact ⟨by omega,by omega⟩
    · rw [layout.entrySize]; exact ⟨by omega,by omega⟩
    · intro equal
      have sizes := congrArg Prod.snd equal
      rw [layout.entrySize] at sizes
      omega

#print axioms DataSlot.disjoint_index
end Binary.Pair.Index
