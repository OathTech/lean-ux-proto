import AllowedipsCoverage
import AllowedipsEntryStack

namespace Binary.AllowedipsEntryContext
open TrustBase CommonBitsCoverage

/-- A whole eight-byte slot inside lookup's deepest real stack footprint. -/
theorem slot_inside (s : MachineState) (n : Nat) (lower : 8≤n) (upper : n≤144)
    (a : BitVec 64) (inside : InRange (s.data.regs.rsp.toBitVec-.ofNat 64 n) 8 a) :
    AllowedipsStackWrites s a := by
  obtain ⟨i,hi,eq⟩ := inside
  refine ⟨144-n+i,by omega,?_⟩
  have number : 144 = n+(144-n) := by omega
  have word : 144#64 = .ofNat 64 n + .ofNat 64 (144-n) := by
    rw [←BitVec.ofNat_add,←number]
  have shift : s.data.regs.rsp.toBitVec-144+.ofNat 64 (144-n) =
      s.data.regs.rsp.toBitVec-.ofNat 64 n := by
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word,←BitVec.sub_sub,BitVec.sub_add_cancel]
  simpa only [BitVec.ofNat_add,←BitVec.add_assoc,shift] using eq

theorem stack_live (s : MachineState) (a : BitVec 64)
    (inside : AllowedipsStackWrites s a) : AllowedipsLiveStack s a := by
  obtain ⟨i,hi,eq⟩ := inside
  exact ⟨i,by omega,eq⟩

theorem prologue_stack {c coverage old ra s world v}
    (pre : AllowedipsEntry c coverage old ra s world v) :
    ∀ i<8, (s.data.dmem.loadInt (Allowedips.entrySlot s.data i) 8).isSome = true := by
  intro i hi
  unfold Allowedips.entrySlot
  split
  · exact pre.stack i (by omega)
  · split
    · simpa using pre.stack 8 (by decide)
    · simpa using pre.stack 10 (by decide)

/-- Readiness of the first callback is derived from entry bytes and the
seven proved prologue stores, with no service premise at a future state. -/
theorem first_ready {c coverage old ra s world v}
    (pre : AllowedipsEntry c coverage old ra s world v) (t : MachineData)
    (memory : t.dmem = Allowedips.entryMemory s.data 7)
    (stack : t.regs.rsp = s.data.regs.rsp-80) :
    CallsReady ⟨coverage,old⟩ t := by
  have frame := Allowedips.entryMemory_frame s.data 7 (by decide)
  have stackSubset (a : BitVec 64) (inside : InRange (s.data.regs.rsp.toBitVec-88) 88 a) :
      AllowedipsStackWrites s a := by
    obtain ⟨i,hi,eq⟩ := inside
    refine ⟨56+i,by omega,?_⟩
    have h : (144 : BitVec 64) = 88+56 := rfl
    rw [BitVec.ofNat_add,←BitVec.add_assoc,h,←BitVec.sub_sub]
    simp only [BitVec.ofNat_eq_ofNat,BitVec.sub_add_cancel]
    exact eq
  have context : (Context.mk coverage old).At s.data.dmem := ⟨pre.coverageBefore,pre.preemptField⟩
  have nextContext := state_frame ⟨coverage,old⟩ s.data.dmem (Allowedips.entryMemory s.data 7)
    context _ frame (by
      intro a member inside
      exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member) (stackSubset a inside))
  have push : t.regs.rsp.toBitVec-8 = s.data.regs.rsp.toBitVec-88 := by
    rw [stack,UInt64.toBitVec_sub]
    change (s.data.regs.rsp.toBitVec-80)-8 = s.data.regs.rsp.toBitVec-88
    rw [BitVec.sub_sub]
    rfl
  refine ⟨by simpa only [memory] using nextContext,?_,?_,?_,?_,?_,?_⟩
  · rw [stack]
    simp only [UInt64.toNat_sub,show (80 : UInt64).toNat = 80 from rfl]
    have aligned := pre.entry.1
    have bound := s.data.regs.rsp.toNat_lt_size
    omega
  · rw [memory,push]
    exact Allowedips.entryMemory_mapped s.data 7 _ (pre.stack 10 (by decide))
  · intro a member inside
    rw [push] at inside
    exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member)
      (slot_inside s 88 (by decide) (by decide) a inside)
  · intro a written inside
    rw [push] at inside
    exact pre.bufferStack a ⟨.inl written.1,written.2⟩
      (stack_live s a (slot_inside s 88 (by decide) (by decide) a inside))
  · intro a written metadata
    exact pre.bufferMetadata a ⟨.inl written.1,written.2⟩ (AllowedipsCoverage.metadata_before coverage old a metadata)
  · intro a written inside
    exact pre.bufferPreempt a ⟨.inl written.1,written.2⟩ inside

#print axioms first_ready
end Binary.AllowedipsEntryContext
