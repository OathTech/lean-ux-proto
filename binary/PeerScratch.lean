import StackFrame

namespace Binary.PeerGet

def ScratchMapped (initial : MachineData) (memory : Mem 64) : Prop :=
  ∀ a, InRange (initial.regs.rsp.toBitVec-56) 56 a → (memory.get? a).isSome = true

/-- Six saved registers and the final callback return slot supply all bytes
    of helper scratch after return, even when the later output aliases it. -/
theorem scratch_slots_mapped (initial : MachineData) (memory : Mem 64)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial 7) memory)
    (separate : ∀ a, InRange (initial.regs.rsp.toBitVec-48) 56 a → ¬writes a)
    (bottom : (memory.loadInt (initial.regs.rsp.toBitVec-56) 8).isSome = true) :
    ∀ n < 7, (memory.loadInt (slot initial n) 8).isSome = true := by
  intro n bound
  by_cases last : n = 6
  · subst n
    exact bottom
  · have nlt : n < 6 := by omega
    have same := frame.loadInt (slot initial n) 8 (by
      intro i hi
      apply separate
      refine ⟨8*(5-n)+i, by omega, ?_⟩
      simp only [slot_restore_window initial n nlt, BitVec.ofNat_add, BitVec.add_assoc])
    rw [← same, saveMemory_read initial 7 n (by decide) bound]
    rfl

theorem scratch_bytes_mapped (initial : MachineData) (memory : Mem 64)
    (mapped : ∀ n < 7, (memory.loadInt (slot initial n) 8).isSome = true) :
    ∀ a, InRange (initial.regs.rsp.toBitVec-56) 56 a → (memory.get? a).isSome = true := by
  rintro a ⟨i, bound, rfl⟩
  have quotient : i / 8 < 7 := by omega
  have h := (loadInt_defined _ _ _).mp (mapped (6-i/8) (by omega)) (i%8) (by omega)
  rw [slot_window initial (6-i/8) (by omega), show 6-(6-i/8)=i/8 by omega] at h
  have offset : BitVec.ofNat 64 (8*(i/8)) + BitVec.ofNat 64 (i%8) = BitVec.ofNat 64 i := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  simpa only [BitVec.add_assoc, offset] using h

#print axioms scratch_slots_mapped
#print axioms scratch_bytes_mapped
end Binary.PeerGet
