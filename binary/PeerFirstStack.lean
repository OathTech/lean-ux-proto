import FirstScanFrame

namespace Binary.PeerGet.First
open Callback LookupHistory.First

/-- The seven saved/call slots and the incoming stack pointer. These are
proof-local stack positions, derived from lookup's unchanged entry frame. -/
def StackSlots (outer sp : UInt64) : Prop :=
  ∀ n ∈ ([0,8,16,24,32,40,48,56] : List UInt64), sp-n≠outer+8

theorem guard_equal {a b outer : UInt64} (safe : a≠outer+8)
    (equal : a.toBitVec=b.toBitVec) : b≠outer+8 := by
  rw [←UInt64.toBitVec_inj.mp equal]
  exact safe

macro "slots_guard " safe:term : tactic => `(tactic|
  first
  | (apply guard_equal ($safe 0 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 8 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 16 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 24 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 32 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 40 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 48 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done)
  | (apply guard_equal ($safe 56 (by decide))
     simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]; done))

theorem StackSlots.call {outer initial body : UInt64} (safe : StackSlots outer initial)
    (stack : body=initial-48) : CallStackSafe outer body := by
  constructor
  · rw [stack]; exact safe 48 (by simp)
  · have same : body-8=initial-56 := by
      rw [stack]
      apply UInt64.toBitVec_inj.mp
      simp only [UInt64.toBitVec_sub,BitVec.sub_sub]
      rfl
    rw [same]; exact safe 56 (by simp)

/-- A lookup helper is called one word below its five saved registers. -/
theorem lookup_slots (outer : UInt64) : StackSlots outer (outer-48) := by
  intro n member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> stack_not_return

end Binary.PeerGet.First
