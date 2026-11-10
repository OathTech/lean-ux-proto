import C1TrunkRegions
/-! Result C1, package 2: the straight-line regions of `add` on a nonempty
root that the trial did not cover: the walk's setup (+0x66, +0x83), the
allocation at :205 (+0x125, +0x133, +0x144) and the entry of the exact-match
branch (+0x3ca, +0x3d4). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- +0x66: reload the slot, widen the family width, clear the parent word,
load the root through the slot and test it. The root word is read after the
store to `(%rsp)`. -/
theorem walk_setup (s : MachineData) (slot root : BitVec 64) (old : Int)
    (saved : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some slot.toNat)
    (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some old)
    (word : (s.dmem.storeInt s.regs.rsp.toBitVec 8 0).loadInt slot 8=some root.toNat) :
    (Placement.physical Add.r66 0x66 s).All (fun t =>
      t.data.regs={s.regs with
        rax := .ofBitVec slot,
        r15 := .ofBitVec ((s.regs.get (.low .rbp .W8)).setWidth 64),
        rbx := .ofBitVec root} ∧
      t.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 0 ∧
      t.pc=if root=0 then Add.entry+0x12e else Add.entry+0x83) := by
  simp [Placement.physical,Add.r66,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp] at saved mapped word ⊢
  simp [saved,mapped,word,ofInt_bmod_toNat,Effects.All]
  refine ⟨?_,?_⟩ <;> split <;> simp_all [Effects.All,Add.entry] <;> rfl

/-- +0x83: save the family width and the owner in the frame, enter the loop. -/
theorem walk_locals (s : MachineData) (oldWidth oldOwner : Int)
    (mappedWidth : s.dmem.loadInt (s.regs.rsp.toBitVec+0x24) 4=some oldWidth)
    (mappedOwner : (s.dmem.storeInt (s.regs.rsp.toBitVec+0x24) 4
      (s.regs.get (.low .rbp .W32)).toInt).loadInt (s.regs.rsp.toBitVec+0x18) 8=some oldOwner) :
    (Placement.physical Add.r83 0x83 s).All (fun t =>
      t.data.regs=s.regs ∧
      t.data.dmem=(s.dmem.storeInt (s.regs.rsp.toBitVec+0x24) 4 (s.regs.get (.low .rbp .W32)).toInt).storeInt
        (s.regs.rsp.toBitVec+0x18) 8 s.regs.r14.toBitVec.toInt ∧
      t.pc=Add.entry+0xf7) := by
  simp [Placement.physical,Add.r83,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at mappedWidth mappedOwner ⊢
  simp [mappedWidth,mappedOwner,Effects.All,Add.entry]
  rfl

/-- +0x125: arguments of the constant comparison callback and its CALL. -/
theorem const_arguments (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r125 0x125 s).All (fun t =>
      t.data.regs={s.regs with rsi := 0, rdi := 0, rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x12e ∧ t.pc=.ofNat 0xffffffff810f40c0) := by
  simp [Placement.physical,Add.r125,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,StatusFlags.from_result,
    Placement.callMemory,Add.entry] at mapped ⊢
  simp [mapped,Effects.All]
  decide

/-- +0x133: allocator arguments and its CALL (the allocation at :205). -/
theorem node_alloc_arguments (s : MachineData) (old : Int) (cache : BitVec 64)
    (global : s.dmem.loadInt nodeCacheAddress 8=some cache.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r133 0x133 s).All (fun t =>
      t.data.regs={s.regs with rsi := 3520, rdi := .ofBitVec cache, rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x144 ∧ t.pc=.ofNat 0xffffffff81196d20) := by
  simp [Placement.physical,Add.r133,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    Effects.All,Width.bytesv,
    Placement.callMemory,Add.entry,nodeCacheAddress] at global mapped ⊢
  simp [global,mapped,Effects.All]
  decide

/-- +0x144: test the allocation and keep it in the parent word. -/
theorem node_alloc_result (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some old) :
    (Placement.physical Add.r144 0x144 s).All (fun t =>
      t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt ∧
      t.pc=if s.regs.rax.toBitVec=0 then Add.entry+0x692 else Add.entry+0x151) := by
  simp [Placement.physical,Add.r144,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Effects.All,
    StatusFlags.from_result,CondCode.interp,BitVec.toAddressSize,BitVec.signed,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop] at mapped ⊢
  simp [mapped,Effects.All]
  refine ⟨?_,?_⟩ <;> split <;> simp_all [Effects.All,Add.entry] <;> rfl

/-- +0x3ca: reload the owner and CALL the coverage callback. -/
theorem exact_owner (s : MachineData) (owner : BitVec 64) (old : Int)
    (saved : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some owner.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r3ca 0x3ca s).All (fun t =>
      t.data.regs={s.regs with r14 := .ofBitVec owner, rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x3d4 ∧ t.pc=.ofNat 0xffffffff810f31f0) := by
  simp [Placement.physical,Add.r3ca,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,Width.bytesv,
    Placement.callMemory,Add.entry] at saved mapped ⊢
  simp [saved,mapped,Effects.All]
  decide

/-- +0x3d4: arguments of the constant comparison callback on the exact
branch and its CALL. -/
theorem exact_const_arguments (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r3d4 0x3d4 s).All (fun t =>
      t.data.regs={s.regs with rsi := 1, rdi := 0, rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x3e0 ∧ t.pc=.ofNat 0xffffffff810f40c0) := by
  simp [Placement.physical,Add.r3d4,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,StatusFlags.from_result,
    Placement.callMemory,Add.entry] at mapped ⊢
  simp [mapped,Effects.All]
  decide

#print axioms walk_setup
#print axioms walk_locals
#print axioms const_arguments
#print axioms node_alloc_arguments
#print axioms node_alloc_result
#print axioms exact_owner
#print axioms exact_const_arguments

end C1Trunk
