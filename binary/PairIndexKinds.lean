import PairIndexFrame

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- Immutable entry type tags, including currently unlinked allocations.
This is a frame used by the next replacement, not a relation clause. -/
def KindFrame (n : Names) (o : Offsets) (before after : DataMem) : Prop :=
  ∀ owner base, (owner,base) ∈ n.owners → ∀ path,
    word after path (base+o.kind) 4=word before path (base+o.kind) 4

theorem KindFrame.refl (n : Names) (o : Offsets) (m : DataMem) : KindFrame n o m m :=
  fun _ _ _ _ => rfl

theorem KindFrame.trans {n o first second third} (a : KindFrame n o first second)
    (b : KindFrame n o second third) : KindFrame n o first third :=
  fun owner base named path => (b owner base named path).trans (a owner base named path)

theorem StorageFrame.kinds {n o before after} (frame : StorageFrame n o before after)
    (layout : Layout o) : KindFrame n o before after := by
  intro owner base named path
  exact (frame.word (entry_storage named) o.kind 4
    (by rw [layout.kind,layout.entrySize]; omega) path).symm

end Binary.Pair.Index
