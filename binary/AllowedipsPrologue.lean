import AllowedipsRegions
import StackFrame

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

def entrySlot (s : MachineData) (i : Nat) : BitVec 64 :=
  s.regs.rsp.toBitVec - .ofNat 64 (if i<6 then (i+1)*8 else if i=6 then 72 else 88)

def entryWords (s : MachineData) : List UInt64 :=
  [s.regs.r15, s.regs.r14, s.regs.r13, s.regs.r12, s.regs.rbp, s.regs.rbx,
   s.regs.rdi, (AllowedipsImage.Lookup.entry+0x20).toUInt64]

def entryMemory (s : MachineData) : Nat → Mem 64
  | 0 => s.dmem
  | n+1 => (entryMemory s n).storeInt (entrySlot s n) 8
      ((entryWords s)[n]?.getD 0).toBitVec.toInt

theorem entryMemory_mapped (s : MachineData) (n : Nat) (a : BitVec 64)
    (mapped : (s.dmem.loadInt a 8).isSome = true) :
    ((entryMemory s n).loadInt a 8).isSome = true := by
  induction n with
  | zero => exact mapped
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

/-- Six callee saves, the root argument slot, and the first callback's
    return address are the prologue's complete write footprint. -/
theorem prologue (s : MachineData)
    (stack : ∀ i < 8, (s.dmem.loadInt (entrySlot s i) 8).isSome = true) :
    (run AllowedipsImage.Lookup.r00 0 s).All (fun t =>
      t.data.regs = {s.regs with
        r12 := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbp := s.regs.rdx, rsp := s.regs.rsp-88} ∧
      t.data.dmem = entryMemory s 8 ∧ t.pc = .ofNat 0xffffffff810f31f0) := by
  have mapped (n : Nat) (hn : n<8) := entryMemory_mapped s n _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  have h5 := mapped 5 (by decide)
  have h6 := mapped 6 (by decide)
  have h7 := mapped 7 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4 h5 h6 h7
  obtain ⟨v0,h0⟩ := h0
  obtain ⟨v1,h1⟩ := h1
  obtain ⟨v2,h2⟩ := h2
  obtain ⟨v3,h3⟩ := h3
  obtain ⟨v4,h4⟩ := h4
  obtain ⟨v5,h5⟩ := h5
  obtain ⟨v6,h6⟩ := h6
  obtain ⟨v7,h7⟩ := h7
  simp [run, AllowedipsImage.Lookup.r00, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add,
    Effects.All, Width.bytesv, AllowedipsImage.Lookup.entry,
    entryMemory, entryWords, entrySlot, BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  simp_all [Effects.All]
  have addressCast (a : BitVec 64) : BitVec.ofInt 64 ((a.toInt-80).bmod 18446744073709551616) = a-80 := by
    have value := BitVec.toInt_sub (x:=a) (y:=80#64)
    change (a-80).toInt = (a.toInt-80).bmod 18446744073709551616 at value
    rw [← value]
    exact BitVec.ofInt_toInt
  simp only [addressCast]
  have address (a : BitVec 64) : a-80#64+8#64=a-72#64 := by
    have h : 80#64 = 72#64+8#64 := rfl
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [address]
  simp only [h6, h7, Effects.All]
  decide

theorem prologuePrefix (s : MachineData)
    (stack : ∀ i < 7, (s.dmem.loadInt (entrySlot s i) 8).isSome = true) :
    (run (AllowedipsImage.Lookup.r00.take 11) 0 s).All (fun t =>
      t.data.regs = {s.regs with
        r12 := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbp := s.regs.rdx, rsp := s.regs.rsp-80} ∧
      t.data.dmem = entryMemory s 7 ∧ t.pc = AllowedipsImage.Lookup.entry+0x1b) := by
  have mapped (n : Nat) (hn : n<7) := entryMemory_mapped s n _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  have h5 := mapped 5 (by decide)
  have h6 := mapped 6 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4 h5 h6
  obtain ⟨v0,h0⟩ := h0
  obtain ⟨v1,h1⟩ := h1
  obtain ⟨v2,h2⟩ := h2
  obtain ⟨v3,h3⟩ := h3
  obtain ⟨v4,h4⟩ := h4
  obtain ⟨v5,h5⟩ := h5
  obtain ⟨v6,h6⟩ := h6
  simp [run, AllowedipsImage.Lookup.r00, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take,  ConstExpr.interp,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add,
    Effects.All, Width.bytesv, AllowedipsImage.Lookup.entry,
    entryMemory, entryWords, entrySlot, BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp_all [Effects.All]
  have addressCast (a : BitVec 64) : BitVec.ofInt 64 ((a.toInt-80).bmod 18446744073709551616) = a-80 := by
    have value := BitVec.toInt_sub (x:=a) (y:=80#64)
    change (a-80).toInt = (a.toInt-80).bmod 18446744073709551616 at value
    rw [← value]
    exact BitVec.ofInt_toInt
  simp only [addressCast]
  have address (a : BitVec 64) : a-80#64+8#64=a-72#64 := by
    have h : 80#64 = 72#64+8#64 := rfl
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [address]
  simp only [h6, Effects.All]
  decide

#print axioms prologuePrefix

#print axioms prologue
end Binary.Allowedips
