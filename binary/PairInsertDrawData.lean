import PairInsertRetryState
import PairInsertOwnership

namespace Binary.Pair.Insert
open Leanux Leanux.WG Index

/-- Rejected draws leave the resident allocation available for the next
attempt. Its index is mapped and updated but is not a table member. -/
theorem RetryData.draw {n o m d owner base} (ready : RetryData n o m d owner base)
    (value : Nat) (small : value<2^32) (storage : storageCheck n o=true) :
    RetryData n o (ready.entry.afterDraw value) d owner base := by
  have layout := (validate_basic (reconstruct_components ready.related).1).1
  let fresh := ready.entry
  have bounded := entry_bound storage fresh.named
  rw [layout.entrySize] at bounded
  refine ⟨fresh.draw_reconstruct value ready.related storage,?_,⟨ready.resident.named,?_,?_,?_⟩,?_⟩
  · rw [fresh.draw_ownership value layout storage]
    exact ready.owned
  · change word (fresh.afterDraw value) "insert.kind" (fresh.base+o.kind) 4=.ok (ownerKind owner)
    rw [layout.kind,fresh.draw_data value layout storage
      (.entry owner fresh.base 24 4 fresh.named (.inr (.inl rfl))) (by omega)]
    simpa only [fresh,RetryData.entry,layout.kind] using ready.resident.kind
  · obtain ⟨next,read⟩ := ready.resident.next
    refine ⟨next,?_⟩
    change word (fresh.afterDraw value) "insert.next" (fresh.link+o.next) 8=.ok next
    rw [fresh.draw_link value layout storage (fresh.nextSlot layout)]
    exact read
  · refine ⟨value,?_⟩
    rw [layout.index]
    apply word_write32_same _ _ _ _ _ small
    simpa only [fresh,RetryData.entry,Nat.add_assoc] using bounded
  · change word (fresh.afterDraw value) "owner.pprev" (fresh.link+o.pprev) 8=.ok 0
    rw [fresh.draw_link value layout storage (fresh.backSlot layout)]
    exact ready.unlinked

#print axioms RetryData.draw
end Binary.Pair.Insert
