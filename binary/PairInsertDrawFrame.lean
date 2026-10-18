import PairInsertDrawData
import PairIndexKinds

namespace Binary.Pair.Index

theorem UnlinkedEntry.draw_heap_frame {n o m} (f : UnlinkedEntry n o m)
    (value : Nat) (layout : Layout o) : EqualOutside (HeapBytes n o) m (f.afterDraw value) := by
  have slot : DataSlot n o (f.base+28) 4 := .entry f.owner f.base 28 4 f.named (.inr (.inr rfl))
  intro a outside
  exact storeInt_frame m (.ofNat 64 (f.base+28)) 4 _ a
    (fun inside => outside (slot.heap layout a inside))

theorem UnlinkedEntry.draw_kind_frame {n o m} (f : UnlinkedEntry n o m)
    (value : Nat) (layout : Layout o) (storage : storageCheck n o=true) :
    KindFrame n o m (f.afterDraw value) := by
  intro owner base named path
  rw [layout.kind]
  exact f.draw_data value layout storage (.entry owner base 24 4 named (.inr (.inl rfl)))
    (entry_address_ne storage named f.named (by rw [layout.entrySize]; decide)
      (by rw [layout.entrySize]; decide) (fun _ => by decide)) path

#print axioms UnlinkedEntry.draw_heap_frame
#print axioms UnlinkedEntry.draw_kind_frame
end Binary.Pair.Index
