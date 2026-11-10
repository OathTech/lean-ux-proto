import AllowedipsPlacementCalls
import AllowedipsChild

/-! Result C1, work package 3, prefix: the straight-line regions between the
selector and the comparison after `common_bits` (`add+0x241`, `+0x24b`,
`+0x25a`) and the root sub-case's block (`add+0x606`), as executions of the
image's directives. -/
namespace Binary.Statements.C1.Proof
open Binary.Pair Binary.Pair.Allowedips Binary.Pair.Allowedips.Placement Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- `mov %r8,0x18(%rsp)` at `add+0x241`. -/
theorem save241 (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some old) :
    (physical (Add.r241.take 1) 0x241 s).All (fun t =>
      t.pc=Add.entry+0x246 ∧ t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+0x18) 8 s.regs.r8.toBitVec.toInt) := by
  simp [physical,Add.r241,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at mapped ⊢
  simp [mapped,Effects.All,Add.entry]

/-- `mov (%rsp),%rdi; mov %r13,%rsi; mov %r15d,%edx` at `add+0x24b`. -/
theorem args24b (s : MachineData) (down : BitVec 64)
    (read : s.dmem.loadInt s.regs.rsp.toBitVec 8=some down.toNat) :
    (physical (Add.r24b.take 3) 0x24b s).All (fun t =>
      t.pc=Add.entry+0x255 ∧ t.data.regs={s.regs with
        rdi := .ofBitVec down,rsi := s.regs.r13,
        rdx := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64)} ∧
      t.data.dmem=s.dmem) := by
  simp [physical,Add.r24b,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,Effects.All] at read ⊢
  simp [read,Effects.All,Add.entry]

/-- `mov %r12d,%edi; mov %eax,%esi; mov %eax,%r13d; call __sanitizer_cov_trace_cmp1` at `add+0x25a`. -/
theorem cmp25a (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (physical Add.r25a 0x25a s).All (fun t =>
      let answer := UInt64.ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64)
      t.data.regs={s.regs with
        rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64),
        r13 := answer,rsi := answer,rsp := s.regs.rsp-8} ∧
      t.data.dmem=callMemory s 0x267 ∧ t.pc=.ofNat 0xffffffff810f4040) := by
  simp at mapped
  simp [physical,Add.r25a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,callMemory,Add.entry,mapped]
  decide

/-- The root sub-case's block at `add+0x606`: the root pointer is loaded
through the saved slot pointer at `rsp+8` and saved at `rsp`. -/
theorem root606 (s : MachineData) (slot base root : BitVec 64) (old : Int)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x8) 8=some slot.toNat)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some base.toNat)
    (rootRead : s.dmem.loadInt slot 8=some root.toNat)
    (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some old) :
    (physical Add.r606 0x606 s).All (fun t =>
      t.pc=Add.entry+0x241 ∧ t.data.regs={s.regs with rax := .ofBitVec root,r8 := .ofBitVec base} ∧
      t.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 root.toInt) := by
  simp [physical,Add.r606,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at slotRead baseRead rootRead mapped ⊢
  have pointer : BitVec.ofInt 64 ((slot.toNat : Int).bmod 18446744073709551616)=slot := by
    rw [Binary.AllowedipsChild.ofInt_bmod64]
    simp
  simp [slotRead,baseRead,pointer,rootRead,mapped,Effects.All,Add.entry]
  constructor
  · decide
  · simp [BitVec.toInt_eq_toNat_bmod]

#print axioms save241
#print axioms args24b
#print axioms cmp25a
#print axioms root606
end Binary.Statements.C1.Proof
