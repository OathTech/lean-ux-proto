import C1Trunk.Stack
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied): the straight-line regions between the prologue and the allocation boundary. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- +0x2a: arguments of the cidr/bits comparison callback and its CALL. -/
theorem cmp_arguments (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r2a 0x2a s).All (fun t =>
      t.data.regs={s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rdi := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64),
        rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x34 ∧ t.pc=.ofNat 0xffffffff810f4040) := by
  simp [Placement.physical,Add.r2a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,
    Placement.callMemory,Add.entry] at mapped ⊢
  simp [mapped,Effects.All]
  decide

/-- +0x34: `cidr > bits` guard. -/
theorem cidr_guard (s : MachineData) :
    (Placement.physical Add.r34 0x34 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=if (s.regs.get (.low .rbp .W8)).toNat < (s.regs.get (.low .r15 .W8)).toNat
        then Add.entry+0x544 else Add.entry+0x3d) := by
  simp [Placement.physical,Add.r34,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,Allowedips.carry8]
  split <;> simp_all [Effects.All,Add.entry]
  all_goals rfl

/-- +0x42: `!peer` guard. -/
theorem peer_guard (s : MachineData) :
    (Placement.physical Add.r42 0x42 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=if s.regs.r14.toBitVec=0 then Add.entry+0x544 else Add.entry+0x4b) := by
  simp [Placement.physical,Add.r42,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  split <;> simp_all [Effects.All,Add.entry]
  all_goals rfl

theorem ofInt_bmod_toNat (x : BitVec 64) :
    BitVec.ofInt 64 ((x.toNat : Int).bmod 18446744073709551616) = x := by
  have h : (x.toNat : Int).bmod 18446744073709551616 = x.toInt := by
    rw [BitVec.toInt_eq_toNat_bmod]
  rw [h]; exact BitVec.ofInt_toInt

/-- +0x50: load the root through the saved slot and test it. -/
theorem root_load (s : MachineData) (slot root : BitVec 64)
    (saved : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some slot.toNat)
    (word : s.dmem.loadInt slot 8=some root.toNat) :
    (Placement.physical Add.r50 0x50 s).All (fun t =>
      t.data.regs={s.regs with rax := .ofBitVec root} ∧ t.data.dmem=s.dmem ∧
      t.pc=if root=0 then Add.entry+0x41c else Add.entry+0x61) := by
  simp [Placement.physical,Add.r50,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp] at saved word ⊢
  simp [saved,word,ofInt_bmod_toNat,Effects.All]
  refine ⟨?_,?_⟩ <;> split <;> simp_all [Effects.All,Add.entry] <;> rfl

/-- The `node_cache` global read rip-relatively at +0x421. -/
def nodeCacheAddress : BitVec 64 := 18446744071595474528#64

/-- +0x421: allocator arguments and its CALL. -/
theorem alloc_arguments (s : MachineData) (old : Int) (cache : BitVec 64)
    (global : s.dmem.loadInt nodeCacheAddress 8=some cache.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (Placement.physical Add.r421 0x421 s).All (fun t =>
      t.data.regs={s.regs with rsi := 3520, rdi := .ofBitVec cache, rsp := s.regs.rsp-8} ∧
      t.data.dmem=Placement.callMemory s 0x432 ∧ t.pc=.ofNat 0xffffffff81196d20) := by
  simp [Placement.physical,Add.r421,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    Effects.All,Width.bytesv,
    Placement.callMemory,Add.entry,nodeCacheAddress] at global mapped ⊢
  simp [global,mapped,Effects.All]
  decide

/-- +0x432: keep the allocation in rbx and test it. -/
theorem alloc_result (s : MachineData) :
    (Placement.physical Add.r432 0x432 s).All (fun t =>
      t.data.regs={s.regs with rbx := s.regs.rax} ∧ t.data.dmem=s.dmem ∧
      t.pc=if s.regs.rax.toBitVec=0 then Add.entry+0x692 else Add.entry+0x43e) := by
  simp [Placement.physical,Add.r432,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,Effects.All,
    StatusFlags.from_result,CondCode.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  refine ⟨?_,?_⟩ <;> split <;> simp_all [Effects.All,Add.entry] <;> rfl

#print axioms cmp_arguments
#print axioms cidr_guard
#print axioms peer_guard
#print axioms root_load
#print axioms alloc_arguments
#print axioms alloc_result

end C1Trunk
