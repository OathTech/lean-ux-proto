import AllowedipsMoves

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

def zeroHigh (s : MachineData) : Mem 64 :=
  s.dmem.storeInt (s.regs.rsp.toBitVec+16) 8 0

theorem initializeQuery (s : MachineData) (oldHigh oldLow : Int)
    (mappedHigh : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8 = some oldHigh)
    (mappedLow : (zeroHigh s).loadInt (s.regs.rsp.toBitVec+24) 8 = some oldLow) :
    (run (AllowedipsImage.Lookup.r20.take 4) 0x20 s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 32} ∧
      t.data.dmem = (zeroHigh s).storeInt (s.regs.rsp.toBitVec+24) 8 0 ∧
      t.pc = AllowedipsImage.Lookup.entry+0x39) := by
  simp [run, AllowedipsImage.Lookup.r20, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop, BitVec.toAddressSize,
    BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add, BitVec.ofInt_ofNat,
    Effects.All, AllowedipsImage.Lookup.entry] at mappedHigh ⊢
  rw [mappedHigh]
  change Effects.All _ (match (zeroHigh s).loadInt (s.regs.rsp.toBitVec+24) 8 with
    | some _ => _ | none => _)
  rw [mappedLow]
  simp [Effects.All,zeroHigh]

theorem compare128Arguments (s : MachineData) :
    (run (AllowedipsImage.Lookup.r4c.take 2) 0x4c s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x53) := by
  simp [run, AllowedipsImage.Lookup.r4c, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, MachineData.setReg, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.take, BitVec.drop, Effects.All, AllowedipsImage.Lookup.entry]

theorem clearFound (s : MachineData) :
    (run AllowedipsImage.Lookup.r8c 0x8c s).All (fun t =>
      t.data.regs = {s.regs with rbp := 0} ∧ t.data.dmem = s.dmem ∧
      t.pc = AllowedipsImage.Lookup.entry+0xd5) := by
  have target : label "L_ffffffff813a0b05" = AllowedipsImage.Lookup.entry+0xd5 := by decide
  simp [run, AllowedipsImage.Lookup.r8c, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.take, BitVec.drop, Effects.All, target, AllowedipsImage.Lookup.entry]

theorem enableArguments (s : MachineData) :
    (run (AllowedipsImage.Lookup.r12b.take 2) 0x12b s).All (fun t =>
      t.data.regs = {s.regs with rsi := 512, rdi := (AllowedipsImage.Lookup.entry+0x137).toUInt64} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x137) := by
  simp [run, AllowedipsImage.Lookup.r12b, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp,  Operand.interp,
    MachineData.set, MachineData.setReg, AddrExpr.interp, ConstExpr.interp,
      Reg64s.set, Reg64s.set64,


    Effects.All, AllowedipsImage.Lookup.entry]
  decide

#print axioms initializeQuery
#print axioms compare128Arguments
#print axioms clearFound
#print axioms enableArguments
end Binary.Allowedips
