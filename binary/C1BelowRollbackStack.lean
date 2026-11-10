import C1BelowFlight

/-! Result C1, work package 3, rollback path: where the two stack words the
rollback writes (the callbacks' return word below `rsp` and the local at
`rsp`) lie, and the arena membership of handed-out nodes. Arithmetic only. -/
namespace Binary.Statements.C1.Proof.Rollback
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- The caller's window does not wrap: `insertReady` checks its span against the heap. -/
theorem window_bounds (facts : ReadyFacts L A c s family ra) :
    insertWindow + A.depth ≤ s.data.regs.rsp.toNat ∧ s.data.regs.rsp.toNat + 8 ≤ 2^64 := by
  have member : (L.table+AllowedipsMutationLayout.root4,8) ∈ L.heap := by
    apply List.mem_append_left
    apply List.mem_append_left
    simp [tableFields]
  have checked := List.all_eq_true.mp (List.all_eq_true.mp facts.heapApart _ member) (ownWindow A s)
    (by simp)
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
  have fit := checked.1.2
  have bound := s.data.regs.rsp.toBitVec.isLt
  have rsp : s.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toNat := rfl
  simp only [ownWindow,BitVec.toNat_sub,BitVec.toNat_ofNat,rsp] at fit
  omega

/-- The word below the stack pointer and the word at it. -/
def Words (rsp : UInt64) (x : BitVec 64) : Prop := InRange (rsp.toBitVec - 8) 16 x

theorem words_push {rsp : UInt64} {x : BitVec 64} (inside : InRange (rsp.toBitVec - 8) 8 x) : Words rsp x := by
  obtain ⟨i,bound,at_⟩ := inside
  exact ⟨i,by omega,at_⟩

theorem words_local {rsp : UInt64} {x : BitVec 64} (inside : InRange rsp.toBitVec 8 x) : Words rsp x := by
  obtain ⟨i,bound,at_⟩ := inside
  refine ⟨i+8,by omega,?_⟩
  rw [at_,BitVec.ofNat_add,BitVec.add_comm (BitVec.ofNat 64 i),←BitVec.add_assoc]
  congr 1
  exact (BitVec.sub_add_cancel _ _).symm

/-- The local at `rsp` is apart from the return word below it. -/
theorem local_push_apart {rsp : UInt64} {x : BitVec 64} (inside : InRange rsp.toBitVec 8 x) :
    ¬InRange (rsp.toBitVec - 8) 8 x := by
  obtain ⟨i,bound,at_⟩ := inside
  rintro ⟨j,other,equal⟩
  have raw := congrArg BitVec.toNat (at_.symm.trans equal)
  have size := rsp.toBitVec.isLt
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat,eight] at raw
  omega

/-- With the frame inside the window, the two words are scratch. -/
theorem words_scratch {a : MachineState} (facts : ReadyFacts L A c s family ra)
    (high : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow)
    {x : BitVec 64} (inside : Words a.data.regs.rsp x) : Scratch s (insertWindow + A.depth) x := by
  obtain ⟨i,bound,at_⟩ := inside
  have window := window_bounds facts
  have size := a.data.regs.rsp.toBitVec.isLt
  have rsp : a.data.regs.rsp.toBitVec.toNat = a.data.regs.rsp.toNat := rfl
  have value := congrArg BitVec.toNat at_
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat,rsp,eight] at value
  unfold insertWindow at low window ⊢
  apply scratch_nat <;> omega

/-- The stack pointer after a call's push. -/
theorem pushed_rsp {a : MachineState} (facts : ReadyFacts L A c s family ra)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow) :
    (a.data.regs.rsp - 8).toNat + 8 = a.data.regs.rsp.toNat := by
  have window := window_bounds facts
  have size := a.data.regs.rsp.toNat_lt_size
  unfold insertWindow at low window
  simp only [UInt64.toNat_sub,UInt64.size] at size ⊢
  have eight : (8 : UInt64).toNat = 8 := rfl
  rw [eight]
  omega

/-- A byte of a handed-out node is in the arena, hence in the heap. -/
theorem kept_arena {live : List Nat} (arena : ∀ node ∈ live, InArena L node) {x : BitVec 64}
    (kept : Kept live x) : L.Arena x := by
  obtain ⟨object,member,i,bound,at_⟩ := kept
  obtain ⟨span,named,lower,upper⟩ := arena object member
  unfold nodeSize at bound upper
  refine ⟨span,named,object+i-span.1,by omega,?_⟩
  rw [at_,←BitVec.ofNat_add,←BitVec.ofNat_add]
  congr 1
  omega

theorem arena_heap {x : BitVec 64} (arena : L.Arena x) : L.Heap x := by
  obtain ⟨span,member,inside⟩ := arena
  exact ⟨span,List.mem_append_right _ member,inside⟩

/-- A handed-out node ends inside the address space: arena spans are checked against the table. -/
theorem live_bound {live : List Nat} (apart : spansApart (objectsOf L) L.arena = true)
    (arena : ∀ node ∈ live, InArena L node) {node : Nat} (member : node ∈ live) : node + nodeSize ≤ 2^64 := by
  obtain ⟨span,named,lower,upper⟩ := arena node member
  have checked := List.all_eq_true.mp (List.all_eq_true.mp apart (L.table,AllowedipsMutationLayout.tableSize)
    (by simp [objectsOf])) span named
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
  have fit := checked.1.2
  omega

/-- Bytes of a node's list words are bytes of the node. -/
theorem node_bytes {base offset size : Nat} (within : offset + size ≤ nodeSize) {x : BitVec 64}
    (inside : InRange (.ofNat 64 base + .ofNat 64 offset) size x) : InRange (.ofNat 64 base) nodeSize x := by
  obtain ⟨i,bound,at_⟩ := inside
  exact ⟨offset+i,by omega,by rw [at_,BitVec.add_assoc,←BitVec.ofNat_add]⟩

#print axioms words_scratch
end Binary.Statements.C1.Proof.Rollback
