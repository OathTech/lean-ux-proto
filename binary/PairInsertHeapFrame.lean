import PairInsertState
import PairWordPlan

namespace Binary.Pair.Index

/-- Equal stores preserve equality on the protected storage cover. No
equality is required for bytes outside that cover. -/
theorem StorageFrame.storeInt {n o before after} (frame : StorageFrame n o before after)
    (address : BitVec 64) (width : Nat) (value : Int) :
    StorageFrame n o (before.storeInt address width value) (after.storeInt address width value) := by
  classical
  intro span member a inside
  have restricted : EqualOutside (fun b => ¬span.contains b) before after := by
    intro b outside
    exact frame span member b (Classical.byContradiction outside)
  exact restricted.storeInt address width value a (fun outside => outside inside)

end Binary.Pair.Index

namespace Binary.Pair.Insert
open Index

theorem Core.store64 {n o c initial ra p shadow s address}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s)
    (layout : Layout o) (slot : LinkSlot n o address) (value : Nat) :
    Core n o c initial ra p (write64 shadow address value) {s with dmem := write64 s.dmem address value} := by
  refine ⟨core.stack,core.table,core.owner,?_,core.frame.storeInt _ _ _,core.outside.storeInt _ _ _⟩
  exact core.memory.frame facts (write64_frame _ _ _) (slot.heap layout)

theorem Core.store32 {n o c initial ra p shadow s address}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s)
    (layout : Layout o) (slot : DataSlot n o address 4) (value : Nat) :
    Core n o c initial ra p (write32 shadow address value) {s with dmem := write32 s.dmem address value} := by
  refine ⟨core.stack,core.table,core.owner,?_,core.frame.storeInt _ _ _,core.outside.storeInt _ _ _⟩
  exact core.memory.frame facts (storeInt_frame _ (.ofNat 64 address) 4 (BitVec.ofNat 32 value).toInt) (slot.heap layout)

#print axioms Core.store64
#print axioms Core.store32
end Binary.Pair.Insert
