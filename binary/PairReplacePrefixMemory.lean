import PairReplacePre

namespace Binary.Pair.Index.ReplaceFocus

theorem prefix_next {n o m} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (path : String) :
    word (replacePrefixMemory m o f.link f.old.previous f.old.next f.old.entry.index)
      path (f.link+o.next) 8=.ok f.old.next := by
  have layout := (validate_basic validated).1
  have table := validate_table_positive validated
  have nextSlot := f.nextSlot layout
  have backSlot := f.backSlot layout
  have previousSlot := f.old.previousSlot layout
  have nextBack : f.link+o.next≠f.link+o.pprev := by rw [layout.next,layout.pprev]; omega
  have different := Ne.symm (f.previous_different layout storage table)
  unfold replacePrefixMemory
  have address : f.link+o.next=f.link := by rw [layout.next,Nat.add_zero]
  rw [word_write64_frame _ _ _ _ _ _ (nextSlot.disjoint previousSlot layout storage different)]
  rw [word_write64_frame _ _ _ _ _ _ (nextSlot.disjoint backSlot layout storage nextBack)]
  exact word_write64_same _ _ _ _ (nextSlot.bounded layout storage) (word_bound f.old.fields.forward)

#print axioms prefix_next
end Binary.Pair.Index.ReplaceFocus
