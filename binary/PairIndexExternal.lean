import PairIndexCallMemory
import PairIndexFrame

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage

def External (c : Context) (initial : MachineState) (words : Nat) (a : BitVec 64) : Prop :=
  StackBytes initial words a ∨ AllowedipsCoverageWrites c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a

theorem Geometry.heap_external {n o c initial words} (g : Geometry n o c initial words) :
    ∀ a, HeapBytes n o a → ¬External c initial words a := by
  intro a heap written
  rcases written with stack | buffer | preempt
  · exact g.heapLive a heap (stack_live stack)
  · exact g.heapService a heap (.inl (.inr ⟨buffer.1,.inr buffer.2⟩))
  · exact g.heapService a heap (.inr preempt)

theorem external_storage {n o c initial words before after}
    (g : Geometry n o c initial words) (frame : EqualOutside (External c initial words) before after) :
    StorageFrame n o before after := by
  apply StorageFrame.of_execution frame
  intro span member a inside
  exact g.heap_external a ⟨span,member,inside⟩

theorem LinkSlot.heap {n o address} (slot : LinkSlot n o address) (layout : Layout o)
    (a : BitVec 64) (inside : InRange (.ofNat 64 address) 8 a) : HeapBytes n o a := by
  cases slot with
  | table b valid =>
    refine ⟨(n.table,o.tableSize),table_storage n o,?_⟩
    have addr : tableHead n o b=n.table+(o.buckets+b*o.headSize+o.first) := by simp [tableHead,Nat.add_assoc]
    rw [addr] at inside
    exact span_slice (by rw [layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega) inside
  | entry owner base offset named offsetIs =>
    refine ⟨(base,o.entrySize),entry_storage named,?_⟩
    exact span_slice (by rw [layout.entrySize]; rcases offsetIs with rfl | rfl <;> omega) inside

theorem external_read {n o c initial words before after base width}
    (g : Geometry n o c initial words) (frame : EqualOutside (External c initial words) before after)
    (heap : ∀ a, InRange base width a → HeapBytes n o a) : before.loadInt base width=after.loadInt base width :=
  frame.loadInt base width (fun i hi => g.heap_external _ (heap _ ⟨i,hi,rfl⟩))

theorem external_trans {c initial words first second third}
    (left : EqualOutside (External c initial words) first second)
    (right : EqualOutside (External c initial words) second third) :
    EqualOutside (External c initial words) first third := fun a outside => (left a outside).trans (right a outside)

theorem at_pc [Labels] {fetch : Int64 → Option Decoded} {s : MachineState} {pc : Int64} {P : MachineState → Prop}
    (equal : s.pc=pc) (run : Eventually (instructionStep fetch) P ⟨s.data,pc⟩) :
    Eventually (instructionStep fetch) P s := by
  cases s
  cases equal
  exact run

#print axioms external_storage
#print axioms LinkSlot.heap
end Binary.Pair.Index
