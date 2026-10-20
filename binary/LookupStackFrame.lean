import StackFrame
import Prologue

namespace Binary.Lookup
def slot (s : MachineData) (i : Nat) : BitVec 64 :=
  s.regs.rsp.toBitVec - .ofNat 64 ((i+1)*8)

theorem slot_window (s : MachineData) (i : Nat) (hi : i < 6) :
    slot s i = (s.regs.rsp.toBitVec - 48) + .ofNat 64 (8*(5-i)) := by
  have number : 48 = (i+1)*8 + 8*(5-i) := by omega
  rw [show (48 : BitVec 64) = .ofNat 64 48 from rfl, number, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rfl

/-- Each pushed word is recovered exactly after all later pushes. This is
    the saved-register/return-word fact needed by the lookup's epilogue. -/
theorem saveMemory_read (s : MachineData) (n i : Nat) (bound : n ≤ 6) (saved : i < n) :
    (saveMemory s n).loadInt (slot s i) 8 =
      some (((savedWords s)[i]?.getD 0).toNat : Int) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i = n
    · subst i
      exact load64_store (saveMemory s n) (slot s n) ((savedWords s)[n]?.getD 0).toBitVec
    · have earlier : i < n := by omega
      have old := ih (by omega) earlier
      have frame := storeInt_frame (saveMemory s n) (slot s n) 8
        ((savedWords s)[n]?.getD 0).toBitVec.toInt
      have read := frame.loadInt (slot s i) 8 (by
        intro byte hb
        rw [slot_window s i (by omega), slot_window s n (by omega)]
        exact stack_slots_disjoint (s.regs.rsp.toBitVec-48) (5-i) (5-n)
          (by omega) (by omega) (by omega) _ ⟨byte, hb, rfl⟩)
      exact read.symm.trans old

theorem saveMemory_frame (s : MachineData) (n : Nat) (bound : n ≤ 6) :
    EqualOutside (InRange (s.regs.rsp.toBitVec - 48) 48) s.dmem (saveMemory s n) := by
  induction n with
  | zero => intro address outside; rfl
  | succ n ih =>
    intro address outside
    have previous := ih (by omega) address outside
    have disjoint : ¬InRange (slot s n) 8 address := by
      rintro ⟨byte, byteBound, atByte⟩
      apply outside
      refine ⟨8*(5-n)+byte, by omega, ?_⟩
      simpa only [slot_window s n (by omega), BitVec.ofNat_add, BitVec.add_assoc] using atByte
    exact previous.trans (storeInt_frame (saveMemory s n) (slot s n) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt address disjoint)

/-- The six pushes never overwrite the caller's original return word. -/
theorem saveMemory_return (s : MachineData) (n : Nat) (bound : n ≤ 6) :
    (saveMemory s n).loadInt s.regs.rsp.toBitVec 8 = s.dmem.loadInt s.regs.rsp.toBitVec 8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have frame := storeInt_frame (saveMemory s n) (slot s n) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt
    have read := frame.loadInt s.regs.rsp.toBitVec 8 (by
      intro byte byteBound
      rw [slot_window s n (by omega)]
      apply stack_slots_disjoint (s.regs.rsp.toBitVec-48) 6 (5-n)
        (by decide) (by omega) (by omega)
      refine ⟨byte, byteBound, ?_⟩
      change s.regs.rsp.toBitVec + .ofNat 64 byte =
        (s.regs.rsp.toBitVec-48+48) + .ofNat 64 byte
      rw [BitVec.sub_add_cancel])
    exact read.symm.trans (ih (by omega))

#print axioms saveMemory_read
#print axioms saveMemory_frame
#print axioms saveMemory_return
end Binary.Lookup
