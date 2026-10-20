import PairInsertEntryFacts
import PairInsertHeapFrame

namespace Binary.Pair.Insert
open Leanux Leanux.WG Index

theorem Resident.frame {n o before after owner base} (resident : Resident n o before owner base)
    (layout : Layout o) (frame : StorageFrame n o before after) : Resident n o after owner base := by
  have same := frame.word (entry_storage resident.named)
  refine ⟨resident.named,?_,?_,?_⟩
  · rw [←same o.kind 4 (by rw [layout.kind,layout.entrySize]; omega)]
    exact resident.kind
  · obtain ⟨next,read⟩ := resident.next
    refine ⟨next,?_⟩
    have eq := same (o.hash+o.next) 8 (by rw [layout.hash,layout.next,layout.entrySize]; omega) "insert.next"
    rw [←Nat.add_assoc] at eq
    rw [←eq]
    exact read
  · obtain ⟨index,read⟩ := resident.index
    rw [←same o.index 4 (by rw [layout.index,layout.entrySize]; omega)]
    exact ⟨index,read⟩

theorem Resident.unhash {n o m owner base} (resident : Resident n o m owner base)
    (layout : Layout o) (storage : storageCheck n o=true) (f : UnlinkFocus n o m) :
    Resident n o (unlinkMemory m o f.removed f.previous f.next) owner base := by
  refine ⟨resident.named,?_,?_,?_⟩
  · have kind := resident.kind
    rw [layout.kind] at kind ⊢
    rw [f.read_data layout storage "insert.kind" (.entry owner base 24 4 resident.named (.inr (.inl rfl)))]
    exact kind
  · obtain ⟨value,oldRead⟩ := resident.next
    have addr : base+o.hash+o.next=base+8 := by rw [layout.hash,layout.next]
    have read := f.read_link layout storage "insert.next" (.entry owner base 8 resident.named (.inl rfl))
    rw [←addr] at read
    rw [oldRead] at read
    split at read
    · exact ⟨0,read⟩
    · split at read
      · exact ⟨f.previous,read⟩
      · split at read
        · exact ⟨f.next,read⟩
        · exact ⟨value,read⟩
  · obtain ⟨value,read⟩ := resident.index
    refine ⟨value,?_⟩
    rw [layout.index] at read ⊢
    rw [f.read_data layout storage "insert.index" (.entry owner base 28 4 resident.named (.inr (.inr rfl)))]
    exact read

#print axioms Resident.frame
#print axioms Resident.unhash
end Binary.Pair.Insert
