import C1TrunkPrologue
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied): readback and frame of the prologue's memory. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage

def slotOffset (i : Nat) : Nat := if i<6 then 88-i*8 else if i=6 then 8 else 16

theorem slot_window (s : MachineData) (i : Nat) (hi : i<8) :
    slot s i = s.regs.rsp.toBitVec-96 + .ofNat 64 (slotOffset i) := by
  unfold slot slotOffset
  split <;> rename_i h
  · have number : 96 = (i+1)*8 + (88-i*8) := by omega
    rw [show (96 : BitVec 64) = .ofNat 64 96 from rfl, number,
      BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  · split <;> rename_i h6
    · change s.regs.rsp.toBitVec-88 = s.regs.rsp.toBitVec-96+8
      have h : (96 : BitVec 64) = 88+8 := rfl
      rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    · change s.regs.rsp.toBitVec-80 = s.regs.rsp.toBitVec-96+16
      have h : (96 : BitVec 64) = 80+16 := rfl
      rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem slot_apart (s : MachineData) (i j : Nat)
    (hi : i<8) (hj : j<8) (different : i≠j) (a : BitVec 64)
    (atI : InRange (slot s i) (slotSize i) a) : ¬InRange (slot s j) (slotSize j) a := by
  rw [slot_window s i hi] at atI
  rw [slot_window s j hj]
  apply InRange.offset_disjoint _ _ _ _ _ (by unfold slotOffset slotSize; repeat' first | split | omega)
    (by unfold slotOffset slotSize; repeat' first | split | omega) _ a atI
  unfold slotOffset slotSize
  repeat' first | split | omega

theorem memory_read (s : MachineData) (n i : Nat) (bound : n≤8) (saved : i<n) (word : i<7) :
    (memory s n).loadInt (slot s i) 8 = some (((words s)[i]?.getD 0).toNat : Int) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i=n
    · subst i
      have size : slotSize n = 8 := by unfold slotSize; split <;> omega
      have value : slotValue s n = ((words s)[n]?.getD 0).toBitVec.toInt := by
        unfold slotValue; split <;> first | omega | rfl
      simp only [memory, size, value]
      exact load64_store _ _ _
    · have previous := ih (by omega) (by omega)
      have frame := storeInt_frame (memory s n) (slot s n) (slotSize n) (slotValue s n)
      have size : slotSize i = 8 := by unfold slotSize; split <;> omega
      exact (frame.loadInt (slot s i) 8 (fun b hb =>
        slot_apart s i n (by omega) (by omega) last _ (size ▸ ⟨b,hb,rfl⟩))).symm.trans previous

theorem memory_cidr (s : MachineData) :
    (memory s 8).loadInt (slot s 7) 4 =
      some ((BitVec.extractLsb' 0 32 s.regs.rcx.toBitVec).toNat : Int) := by
  exact load32_store _ _ _

theorem memory_frame (s : MachineData) (n : Nat) (bound : n≤8) :
    EqualOutside (InRange (s.regs.rsp.toBitVec-96) 96) s.dmem (memory s n) := by
  induction n with
  | zero => intro a outside; rfl
  | succ n ih =>
    intro a outside
    apply (ih (by omega) a outside).trans
    apply storeInt_frame
    rintro ⟨b,hb,eq⟩
    apply outside
    rw [slot_window s n (by omega)] at eq
    refine ⟨slotOffset n+b, ?_, ?_⟩
    · unfold slotOffset slotSize at *; repeat' first | split at hb | split | omega
    · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq

#print axioms memory_read
#print axioms memory_cidr
#print axioms memory_frame
end C1Trunk
