import AllowedipsRootFinish

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def highMemory (s : MachineData) (word : BitVec 64) : DataMem :=
  s.dmem.storeInt (s.regs.rbx.toBitVec+40) 8 word.toInt

theorem copy_high (s : MachineData) (word : BitVec 64)
    (size : s.regs.rax=16) (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (source : s.dmem.loadInt (s.regs.r13.toBitVec+8) 8=some word.toNat)
    (mapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+40) 8).isSome=true) :
    (Placement.physical Add.r4ad 0x4ad s).All (fun t =>
      t.pc=Add.entry+0x4bf ∧ t.data.dmem=highMemory s word ∧
      t.data.regs={s.regs with rax:=15,rdx:=.ofBitVec word}) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r4ad,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    size,dest,BitVec.add_assoc,highMemory] at source read ⊢
  rw [source]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  simp only [AllowedipsChild.ofInt_bmod64,BitVec.ofInt_add,BitVec.ofInt_toInt,
    BitVec.ofInt_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  rw [read]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp,BitVec.unsigned,Add.entry,BitVec.toInt_eq_toNat_bmod]
  all_goals rfl

theorem copy_loop_setup (s : MachineData) (size : s.regs.rax=15) :
    (Placement.physical Add.r4bf 0x4bf s).All (fun t =>
      t.pc=Add.entry+0x4c4 ∧ t.data.dmem=s.dmem ∧ t.data.regs={s.regs with rax:=8,rdx:=0}) := by
  simp [Placement.physical,Add.r4bf,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,size,Add.entry]

def lowMemory (s : MachineData) (word : BitVec 64) : DataMem :=
  s.dmem.storeInt (s.regs.rbx.toBitVec+32) 8 word.toInt

/-- For the two accepted address families the generic copy loop executes
exactly once on the 128-bit branch. -/
theorem copy_low (s : MachineData) (word : BitVec 64)
    (size : s.regs.rax=8) (offset : s.regs.rdx=0)
    (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (source : s.dmem.loadInt s.regs.r13.toBitVec 8=some word.toNat)
    (mapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+32) 8).isSome=true) :
    (Placement.physical Add.r4c4 0x4c4 s).All (fun t =>
      t.pc=Add.entry+0x4d6 ∧ t.data.dmem=lowMemory s word ∧
      t.data.regs={s.regs with rcx:=0,rdx:=8,rdi:=.ofBitVec word}) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r4c4,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,Effects.All,
    size,offset,dest,lowMemory] at source read ⊢
  rw [source]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  simp only [AllowedipsChild.ofInt_bmod64,BitVec.ofInt_add,BitVec.ofInt_toInt,
    BitVec.ofInt_ofNat]
  rw [read]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp,BitVec.unsigned,Add.entry,BitVec.toInt_eq_toNat_bmod]
  all_goals rfl

#print axioms copy_high
#print axioms copy_loop_setup
#print axioms copy_low
end Binary.Pair.Allowedips.Root
