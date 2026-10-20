import AllowedipsRegions
namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

theorem commonArguments (s : MachineData) :
    (run (AllowedipsImage.Lookup.rda.take 3) 0xda s).All (fun t =>
      t.data.regs = {s.regs with
        rdi := s.regs.rbx,
        rdx := .ofBitVec ((s.regs.get (.low .r13 .W32)).setWidth 64),
        rsi := s.regs.rsp+16} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0xe5) := by
  simp [run, AllowedipsImage.Lookup.rda, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, AllowedipsImage.Lookup.entry] at *

theorem rootLoad (s : MachineData) (value : BitVec 64)
    (field : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8 = some value.toNat) :
    (run (AllowedipsImage.Lookup.r79.take 1) 0x79 s).All (fun t =>
      t.data.regs = {s.regs with rbx := .ofBitVec value} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x7e) := by
  simp [run, AllowedipsImage.Lookup.r79, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp,  Reg64s.get64, Reg64s.set, Reg64s.set64,
      BitVec.take,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, AllowedipsImage.Lookup.entry] at *
  rw [field]
  simp [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem selectedPeer (s : MachineData) (value : BitVec 64)
    (field : s.dmem.loadInt (s.regs.rbp.toBitVec+0) 8 = some value.toNat) :
    (run (AllowedipsImage.Lookup.r110.take 1) 0x110 s).All (fun t =>
      t.data.regs = {s.regs with rdi := .ofBitVec value} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x114) := by
  simp [run, AllowedipsImage.Lookup.r110, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp,  Reg64s.get64, Reg64s.set, Reg64s.set64,
      BitVec.take,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
     Effects.All, AllowedipsImage.Lookup.entry] at *
  rw [field]
  simp [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem prefixArguments (s : MachineData) (cidr : BitVec 8)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1 = some cidr.toNat) :
    (run (AllowedipsImage.Lookup.rea.take 4) 0xea s).All (fun t =>
      t.data.regs = {s.regs with
        r15 := .ofBitVec (cidr.setWidth 64),
        r14 := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
        rsi := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
        rdi := .ofBitVec (cidr.setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0xf7) := by
  simp [run, AllowedipsImage.Lookup.rea, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, AllowedipsImage.Lookup.entry] at *
  rw [field]
  simp [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have bound := cidr.isLt
  omega

theorem fullLengthArguments (s : MachineData) :
    (run (AllowedipsImage.Lookup.ra4.take 2) 0xa4 s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64),
        rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0xaa) := by
  simp [run, AllowedipsImage.Lookup.ra4, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.set, MachineData.setReg,
     Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,

     Effects.All, AllowedipsImage.Lookup.entry] at *

#print axioms commonArguments
#print axioms rootLoad
#print axioms selectedPeer
#print axioms prefixArguments
#print axioms fullLengthArguments
end Binary.Allowedips
