import PairInsertRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

theorem call_unhash_bh (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.r54 0x54 s).All (fun t =>
      t.data.regs={s.regs with rsi := 512,rdi := (codeEntry+0x60).toUInt64,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x65).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810732c0) := by
  simp [run,IndexInsertImage.Insert.r54,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    RelRegOrMem.interp,ConstExpr.interp,AddrExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry] at mapped ⊢
  rw [mapped]
  simp only [Effects.All]
  refine ⟨?_,trivial,?_⟩
  · congr 1 <;> decide +kernel
  · decide +kernel

theorem call_nested_bh (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.r160 0x160 s).All (fun t =>
      t.data.regs={s.regs with
        rsi := 512,rdi := (codeEntry+0x16c).toUInt64,
        rbx := (codeEntry+0x16c).toUInt64,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x174).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810732c0) := by
  simp [run,IndexInsertImage.Insert.r160,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,AddrExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry] at mapped ⊢
  rw [mapped]
  simp only [Effects.All]
  refine ⟨?_,trivial,?_⟩
  · congr 1 <;> decide +kernel
  · decide +kernel

theorem call_outer_bh (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.r174 0x174 s).All (fun t =>
      t.data.regs={s.regs with rdi := s.regs.rbx,rsi := 512,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x181).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810732c0) := by
  simp [run,IndexInsertImage.Insert.r174,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry] at mapped ⊢
  rw [mapped]
  simp only [Effects.All]
  decide +kernel

theorem restore_return (s : MachineData) (index : BitVec 32) (bx bp r12 r13 r14 r15 ra : UInt64)
    (read : s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4=some index.toNat)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8=some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8=some r15.toNat)
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8=some ra.toNat) :
    (run IndexInsertImage.Insert.r181 0x181 s).All (fun t =>
      t.data.regs={s.regs with
        rax := .ofNat index.toNat,rbx := bx,rbp := bp,r12 := r12,r13 := r13,r14 := r14,r15 := r15,
        rsp := s.regs.rsp+56} ∧ t.data.dmem=s.dmem ∧ t.pc=ra.toInt64) := by
  simp [run,IndexInsertImage.Insert.r181,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,AddrExpr.interp,ConstExpr.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_ofNat,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry,
    UInt64.toBitVec_add,UInt64.ofBitVec_add,BitVec.add_assoc] at read h0 h1 h2 h3 h4 h5 h6 ⊢
  rw [read]
  simp_all [Effects.All]
  constructor
  · apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp
  · apply Int64.toBitVec_inj.mp
    simp [Int64.toBitVec_ofInt,UInt64.toInt64]
    rfl

#print axioms call_unhash_bh
#print axioms call_nested_bh
#print axioms call_outer_bh
#print axioms restore_return
end Binary.Pair.Insert
