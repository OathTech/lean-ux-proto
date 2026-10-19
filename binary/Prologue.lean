import Regions
import Memory

namespace Binary.Lookup
local instance : Labels := Image.linkedLabels

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r14, s.regs.r13, s.regs.r12, s.regs.rbp, s.regs.rbx,
    (Image.Lookup.entry + 0x19).toUInt64]

def saveMemory (s : MachineData) : Nat → DataMem
  | 0 => s.dmem
  | n + 1 => (saveMemory s n).storeInt
      (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt

theorem saves_preserve_mapped (s : MachineData) (n : Nat) (a : BitVec 64)
    (h : (s.dmem.loadInt a 8).isSome = true) :
    ((saveMemory s n).loadInt a 8).isSome = true := by
  induction n with
  | zero => exact h
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

theorem prologue (s : MachineData)
    (stack : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8).isSome = true) :
    (run Image.Lookup.r00 0 s).All (fun t =>
      t.data.regs = {s.regs with
        r14 := .ofNat (s.regs.get (.low .rsi .W32)).toNat,
        r13 := s.regs.rcx,
        r12 := .ofNat (s.regs.get (.low .rdx .W32)).toNat,
        rbx := s.regs.rdi, rsp := s.regs.rsp - 48} ∧
      t.data.dmem = saveMemory s 6 ∧ t.pc = .ofNat 0xffffffff810f31f0) := by
  have mapped (n : Nat) (hn : n < 6) :=
    saves_preserve_mapped s n _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  have h5 := mapped 5 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4 h5
  obtain ⟨v0, h0⟩ := h0
  obtain ⟨v1, h1⟩ := h1
  obtain ⟨v2, h2⟩ := h2
  obtain ⟨v3, h3⟩ := h3
  obtain ⟨v4, h4⟩ := h4
  obtain ⟨v5, h5⟩ := h5
  simp [run, Image.Lookup.r00, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  Image.Lookup.entry,
    saveMemory, savedWords, BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 ⊢
  simp_all [Effects.All]
  refine ⟨⟨?_, ?_⟩, by rfl⟩
  all_goals apply UInt64.toBitVec_inj.mp
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp

#print axioms prologue
end Binary.Lookup
