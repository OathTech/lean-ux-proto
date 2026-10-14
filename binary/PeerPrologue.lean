import PeerRegions
import Memory

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r15, s.regs.r14, s.regs.r13, s.regs.r12, s.regs.rbp, s.regs.rbx,
    (Image.PeerGet.entry + 0x12).toUInt64]

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
    (stack : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8).isSome = true) :
    (run Image.PeerGet.r00 0 s).All (fun t =>
      t.data.regs = {s.regs with
        rbx := s.regs.rdi, rsp := s.regs.rsp - 56} ∧
      t.data.dmem = saveMemory s 7 ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  have mapped (n : Nat) (hn : n < 7) :=
    saves_preserve_mapped s n _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  have h5 := mapped 5 (by decide)
  have h6 := mapped 6 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4 h5 h6
  obtain ⟨v0, h0⟩ := h0
  obtain ⟨v1, h1⟩ := h1
  obtain ⟨v2, h2⟩ := h2
  obtain ⟨v3, h3⟩ := h3
  obtain ⟨v4, h4⟩ := h4
  obtain ⟨v5, h5⟩ := h5
  obtain ⟨v6, h6⟩ := h6
  simp [run, Image.PeerGet.r00, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv, callMemory, Image.PeerGet.entry,
    saveMemory, savedWords, BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  rfl

#print axioms prologue
end Binary.PeerGet
