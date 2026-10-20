import PairInsertRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

theorem first_arguments (s : MachineData) (index : UInt32) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4=some index.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.ra5 0xa5 s).All (fun t =>
      t.data.regs={s.regs with
        r14 := .ofNat index.toNat,
        rdi := .ofNat (s.regs.get (.low .r13 .W32)).toNat,
        rsi := .ofNat index.toNat,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0xb4).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810f4080) := by
  simp [run,IndexInsertImage.Insert.ra5,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    Reg64s.set,Reg64s.set64,BitVec.drop,BitVec.take,
    RelRegOrMem.interp,ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry]
  simp_all [Effects.All]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp
  · apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp
  · decide +kernel

theorem second_arguments (s : MachineData) (index : UInt32) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4=some index.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.r10a 0x10a s).All (fun t =>
      t.data.regs={s.regs with
        r15 := .ofNat index.toNat,
        rdi := .ofNat (s.regs.get (.low .r13 .W32)).toNat,
        rsi := .ofNat index.toNat,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x119).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810f4080) := by
  simp [run,IndexInsertImage.Insert.r10a,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    Reg64s.set,Reg64s.set64,BitVec.drop,BitVec.take,
    RelRegOrMem.interp,ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry]
  simp_all [Effects.All]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp
  · apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp
  · decide +kernel

#print axioms first_arguments
#print axioms second_arguments
end Binary.Pair.Insert
