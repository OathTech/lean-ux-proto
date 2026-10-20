import AllowedipsNodeHeaderChecked

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def first4Memory (s : MachineData) (value : BitVec 32) : DataMem :=
  s.dmem.storeInt (s.regs.r8.toBitVec+32) 4 value.toInt

theorem copy4_branch (s : MachineData) (bytes : s.regs.rbp=4) :
    (Placement.physical Add.r1de 0x1de s).All (fun t =>
      t.pc=Add.entry+0x740 ∧ t.data.dmem=s.dmem ∧ t.data.regs=s.regs) := by
  simp [Placement.physical,Add.r1de,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,StatusFlags.from_result,CondCode.interp,bytes]
  rfl

theorem copy4 (s : MachineData) (first again : BitVec 32)
    (bytes : s.regs.rbp=4) (dest : s.regs.r14.toBitVec=s.regs.r8.toBitVec+32)
    (firstRead : s.dmem.loadInt s.regs.r13.toBitVec 4=some first.toNat)
    (firstMapped : (s.dmem.loadInt (s.regs.r8.toBitVec+32) 4).isSome=true)
    (againRead : (first4Memory s first).loadInt s.regs.r13.toBitVec 4=some again.toNat)
    (againMapped : ((first4Memory s first).loadInt (s.regs.r8.toBitVec+32) 4).isSome=true) :
    (Placement.physical Add.r740 0x740 s).All (fun t =>
      t.pc=Add.entry+0x1ff ∧
      t.data.dmem=(first4Memory s first).storeInt (s.regs.r8.toBitVec+32) 4 again.toInt ∧
      t.data.regs={s.regs with rax:=.ofBitVec (again.setWidth 64)}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨oldAgain,oldAgainRead⟩ := Option.isSome_iff_exists.mp againMapped
  simp [Placement.physical,Add.r740,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    first4Memory,bytes] at firstRead oldRead againRead oldAgainRead ⊢
  rw [firstRead]
  simp only [Effects.All,AllowedipsChild.extract32]
  rw [oldRead]
  simp only [Effects.All,Root.stored32,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,dest]
  rw [againRead]
  simp only [Effects.All]
  rw [oldAgainRead]
  simp [Effects.All,Add.entry,Root.stored32]
  all_goals rfl

theorem copy6_high (s : MachineData) (value : BitVec 64)
    (bytes : s.regs.rbp=16)
    (read : s.dmem.loadInt (s.regs.r13.toBitVec+8) 8=some value.toNat)
    (mapped : (s.dmem.loadInt (s.regs.r14.toBitVec+8) 8).isSome=true) :
    (Placement.physical Add.r4ed 0x4ed s).All (fun t =>
      t.pc=Add.entry+0x503 ∧
      t.data.dmem=s.dmem.storeInt (s.regs.r14.toBitVec+8) 8 value.toInt ∧
      t.data.regs={s.regs with rax:=.ofBitVec value,rcx:=15}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r4ed,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp,bytes,BitVec.add_assoc] at read oldRead ⊢
  rw [read]
  simp only [Effects.All]
  rw [oldRead]
  simp [Effects.All,Add.entry,BitVec.unsigned,BitVec.toInt_eq_toNat_bmod]

theorem copy6_setup (s : MachineData) (last : s.regs.rcx=15) :
    (Placement.physical Add.r503 0x503 s).All (fun t =>
      t.pc=Add.entry+0x508 ∧ t.data.dmem=s.dmem ∧ t.data.regs={s.regs with rax:=0,rcx:=8}) := by
  simp [Placement.physical,Add.r503,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,ConstExpr.interp,MachineData.set,MachineData.setReg,Reg64s.get,Reg64s.get64,
    Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Effects.All,last,Add.entry]

theorem copy6_low (s : MachineData) (value : BitVec 64)
    (zero : s.regs.rax=0) (limit : s.regs.rcx=8)
    (read : s.dmem.loadInt s.regs.r13.toBitVec 8=some value.toNat)
    (mapped : (s.dmem.loadInt s.regs.r14.toBitVec 8).isSome=true) :
    (Placement.physical Add.r508 0x508 s).All (fun t =>
      t.pc=Add.entry+0x51a ∧ t.data.dmem=s.dmem.storeInt s.regs.r14.toBitVec 8 value.toInt ∧
      t.data.regs={s.regs with rax:=8,rdx:=0,rsi:=.ofBitVec value}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r508,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,Effects.All,
    StatusFlags.from_result,CondCode.interp,zero,limit] at read oldRead ⊢
  rw [read]
  simp only [Effects.All]
  rw [oldRead]
  simp [Effects.All,Add.entry,BitVec.unsigned,BitVec.toInt_eq_toNat_bmod]

theorem copy6_finish (s : MachineData) :
    (Placement.physical Add.r51a 0x51a s).All (fun t =>
      t.pc=Add.entry+0x1ff ∧ t.data=s) := by
  simp [Placement.physical,Add.r51a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  rfl

#print axioms copy4
#print axioms copy6_high
#print axioms copy6_low
end Binary.Pair.Allowedips.NodeInit
