import C1BelowInternalRegions

/-! Result C1, work package 3: the internal node's header store and the
width-dependent copy of the leaf's key from the first node (`add+0x2fb` to
`add+0x31d`), region by region. -/
namespace Binary.Pair.Allowedips.C1Internal
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

/-- `+0x2fb`: the packed header word goes to the node; the family decides
which copy follows. -/
theorem store_region (s : MachineData) (value : BitVec 32) (width : Nat)
    (family : width=32 ∨ width=128) (carry : s.status.cf=decide (width=32))
    (packed : s.regs.rax=.ofBitVec (value.setWidth 64))
    (mapped : (s.dmem.loadInt (s.regs.r12.toBitVec+24) 4).isSome=true) :
    (Placement.physical Add.r2fb 0x2fb s).All (fun t =>
      t.pc=(if width=32 then Add.entry+0x30b else Add.entry+0x61c) ∧
      t.data.dmem=s.dmem.storeInt (s.regs.r12.toBitVec+24) 4 value.toInt ∧
      t.data.regs={s.regs with rdi:=.ofBitVec (s.regs.r12.toBitVec+32)}) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r2fb,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,CondCode.interp,packed,carry,AllowedipsChild.extract32] at read ⊢
  rw [read]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry]
  all_goals rfl

theorem copy4_branch (s : MachineData) (bytes : s.regs.rbp=4) :
    (Placement.physical Add.r30b 0x30b s).All (fun t =>
      t.pc=Add.entry+0x76c ∧ t.data.dmem=s.dmem ∧ t.data.regs=s.regs) := by
  simp [Placement.physical,Add.r30b,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,StatusFlags.from_result,CondCode.interp,bytes]
  rfl

def first4Memory (s : MachineData) (value : BitVec 32) : DataMem :=
  s.dmem.storeInt (s.regs.r12.toBitVec+32) 4 value.toInt

/-- `+0x76c`: the IPv4 key, read twice from the first node as the image does. -/
theorem copy4 (s : MachineData) (first again : BitVec 32)
    (bytes : s.regs.rbp=4) (dest : s.regs.rdi.toBitVec=s.regs.r12.toBitVec+32)
    (source : s.regs.r14.toBitVec=s.regs.r8.toBitVec+32)
    (firstRead : s.dmem.loadInt (s.regs.r8.toBitVec+32) 4=some first.toNat)
    (firstMapped : (s.dmem.loadInt (s.regs.r12.toBitVec+32) 4).isSome=true)
    (againRead : (first4Memory s first).loadInt (s.regs.r8.toBitVec+32) 4=some again.toNat)
    (againMapped : ((first4Memory s first).loadInt (s.regs.r12.toBitVec+32) 4).isSome=true) :
    (Placement.physical Add.r76c 0x76c s).All (fun t =>
      t.pc=Add.entry+0x31d ∧
      t.data.dmem=(first4Memory s first).storeInt (s.regs.r12.toBitVec+32) 4 again.toInt ∧
      t.data.regs={s.regs with rax:=.ofBitVec (again.setWidth 64)}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨oldAgain,oldAgainRead⟩ := Option.isSome_iff_exists.mp againMapped
  simp [Placement.physical,Add.r76c,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    first4Memory,bytes] at firstRead oldRead againRead oldAgainRead ⊢
  rw [firstRead]
  simp only [Effects.All,AllowedipsChild.extract32]
  rw [oldRead]
  simp only [Effects.All,Root.stored32,BitVec.add_assoc,BitVec.reduceAdd,dest,source]
  rw [againRead]
  simp only [Effects.All]
  rw [oldAgainRead]
  simp [Effects.All,Add.entry,Root.stored32]
  all_goals rfl

/-- `+0x61c`: the upper eight key bytes (the last eight of the object's key). -/
theorem copy6_high (s : MachineData) (value : BitVec 64)
    (bytes : s.regs.rbp=16)
    (read : s.dmem.loadInt (s.regs.r14.toBitVec+8) 8=some value.toNat)
    (mapped : (s.dmem.loadInt (s.regs.rdi.toBitVec+8) 8).isSome=true) :
    (Placement.physical Add.r61c 0x61c s).All (fun t =>
      t.pc=Add.entry+0x634 ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rdi.toBitVec+8) 8 value.toInt ∧
      t.data.regs={s.regs with rax:=.ofBitVec value,r9:=15}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r61c,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp,bytes,BitVec.add_assoc] at read oldRead ⊢
  rw [read]
  simp only [Effects.All]
  rw [oldRead]
  simp [Effects.All,Add.entry,BitVec.unsigned,BitVec.toInt_eq_toNat_bmod]

theorem copy6_setup (s : MachineData) (last : s.regs.r9=15) :
    (Placement.physical Add.r634 0x634 s).All (fun t =>
      t.pc=Add.entry+0x63a ∧ t.data.dmem=s.dmem ∧ t.data.regs={s.regs with rax:=0,r9:=8}) := by
  simp [Placement.physical,Add.r634,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,ConstExpr.interp,MachineData.set,MachineData.setReg,Reg64s.get,Reg64s.get64,
    Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Effects.All,last,Add.entry]

/-- `+0x63a`: the lower eight key bytes; one iteration of the word loop. -/
theorem copy6_low (s : MachineData) (value : BitVec 64)
    (zero : s.regs.rax=0) (limit : s.regs.r9=8)
    (read : s.dmem.loadInt s.regs.r14.toBitVec 8=some value.toNat)
    (mapped : (s.dmem.loadInt s.regs.rdi.toBitVec 8).isSome=true) :
    (Placement.physical Add.r63a 0x63a s).All (fun t =>
      t.pc=Add.entry+0x64c ∧ t.data.dmem=s.dmem.storeInt s.regs.rdi.toBitVec 8 value.toInt ∧
      t.data.regs={s.regs with rax:=8,rsi:=0,r10:=.ofBitVec value}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r63a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
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
    (Placement.physical Add.r64c 0x64c s).All (fun t =>
      t.pc=Add.entry+0x31d ∧ t.data=s) := by
  simp [Placement.physical,Add.r64c,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  rfl

end Binary.Pair.Allowedips.C1Internal
