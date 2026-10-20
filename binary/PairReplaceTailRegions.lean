import PairReplaceRegions

namespace Binary.Pair.Replace
local instance : Labels := Image.linkedLabels

theorem call_bh (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexMutatorImage.Replace.r86 0x86 s).All (fun t =>
      t.data.regs={s.regs with rsi := 512,rdi := (codeEntry+0x92).toUInt64,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x97).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810732c0) := by
  simp [run,IndexMutatorImage.Replace.r86,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    RelRegOrMem.interp,ConstExpr.interp,AddrExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexMutatorImage.Replace.entry] at mapped ⊢
  rw [mapped]
  simp only [Effects.All]
  refine ⟨?_,trivial,?_⟩
  · congr 1 <;> decide +kernel
  · decide +kernel

def returnWord (s : MachineData) : UInt64 :=
  .ofBitVec ((s.regs.r13.toBitVec.setWidth 32).setWidth 64)

theorem restore_return (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8=some ra.toNat) :
    (run IndexMutatorImage.Replace.r97 0x97 s).All (fun t =>
      t.data.regs={s.regs with
        rax := returnWord s,rbx := bx,rbp := bp,r12 := r12,r13 := r13,rsp := s.regs.rsp+40} ∧
      t.data.dmem=s.dmem ∧ t.pc=ra.toInt64) := by
  simp [run,IndexMutatorImage.Replace.r97,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,
    Effects.All,Width.bytesv,codeEntry,IndexMutatorImage.Replace.entry,
    UInt64.toBitVec_add,UInt64.ofBitVec_add,BitVec.add_assoc,returnWord] at h0 h1 h2 h3 h4 ⊢
  simp_all [Effects.All]
  constructor
  · rw [←BitVec.setWidth_eq_extractLsb' (by decide : 32≤64)]
  · apply Int64.toBitVec_inj.mp
    simp [Int64.toBitVec_ofInt,UInt64.toInt64]
    rfl

theorem result_low (old : UInt64) (previous : BitVec 64) :
    ((resultWord old previous).toBitVec.setWidth 8) =
      if previous=0 then (0 : BitVec 8) else 1 := by
  change ((old.toBitVec.drop 8) ++ (if previous=0 then (0 : BitVec 8) else 1)).setWidth 8=_
  simp only [BitVec.setWidth_append,show 8≤8 from by decide,↓reduceDIte,BitVec.setWidth_eq]

#print axioms call_bh
#print axioms restore_return
#print axioms result_low
end Binary.Pair.Replace
