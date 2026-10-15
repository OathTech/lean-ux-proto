import AllowedipsPrologue

namespace Binary.Allowedips

/-- Uniform stack coordinates include both argument slots and the caller's
return word. Modular addresses need no no-wrap premise. -/
theorem entrySlot_window (s : MachineData) (i : Nat) (hi : i<8) :
    entrySlot s i = s.regs.rsp.toBitVec-88 +
      .ofNat 64 (if i<6 then 80-i*8 else if i=6 then 16 else 0) := by
  unfold entrySlot
  split <;> rename_i h
  · have number : 88 = (i+1)*8 + (80-i*8) := by omega
    rw [show (88 : BitVec 64) = .ofNat 64 88 from rfl, number,
      BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  · split <;> rename_i h6
    · subst i
      change s.regs.rsp.toBitVec-72 = s.regs.rsp.toBitVec-88+16
      have h : (88 : BitVec 64) = 72+16 := rfl
      rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    · simp

theorem entrySlot_apart (s : MachineData) (i j : Nat)
    (hi : i<8) (hj : j<8) (different : i≠j) (a : BitVec 64)
    (atI : InRange (entrySlot s i) 8 a) : ¬InRange (entrySlot s j) 8 a := by
  rw [entrySlot_window s i hi] at atI
  rw [entrySlot_window s j hj]
  apply InRange.offset_disjoint _ _ _ _ _ (by split <;> (try split) <;> omega)
    (by split <;> (try split) <;> omega) _ a atI
  repeat' first | split | omega

theorem entryMemory_read (s : MachineData) (n i : Nat) (bound : n≤8) (saved : i<n) :
    (entryMemory s n).loadInt (entrySlot s i) 8 =
      some (((entryWords s)[i]?.getD 0).toNat : Int) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i=n
    · subst i
      exact load64_store _ _ _
    · have previous := ih (by omega) (by omega)
      have frame := storeInt_frame (entryMemory s n) (entrySlot s n) 8
        ((entryWords s)[n]?.getD 0).toBitVec.toInt
      exact (frame.loadInt (entrySlot s i) 8 (fun b hb =>
        entrySlot_apart s i n (by omega) (by omega) last _ ⟨b,hb,rfl⟩)).symm.trans previous

theorem entryMemory_frame (s : MachineData) (n : Nat) (bound : n≤8) :
    EqualOutside (InRange (s.regs.rsp.toBitVec-88) 88) s.dmem (entryMemory s n) := by
  induction n with
  | zero => intro a outside; rfl
  | succ n ih =>
    intro a outside
    apply (ih (by omega) a outside).trans
    apply storeInt_frame
    rintro ⟨b,hb,eq⟩
    apply outside
    rw [entrySlot_window s n (by omega)] at eq
    refine ⟨(if n<6 then 80-n*8 else if n=6 then 16 else 0)+b, ?_, ?_⟩
    · split <;> (try split) <;> omega
    · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq

#print axioms entryMemory_read
#print axioms entryMemory_frame
end Binary.Allowedips
