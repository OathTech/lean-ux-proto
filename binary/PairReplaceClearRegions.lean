import PairReplaceRegions

namespace Binary.Pair.Replace
local instance : Labels := Image.linkedLabels

theorem successor_store (s : MachineData) (next : BitVec 64) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbp.toBitVec+8) 8=some next.toNat)
    (mapped : s.dmem.loadInt (next+8) 8=some old) :
    (run IndexMutatorImage.Replace.r56 0x56 s).All (fun t =>
      t.data.regs={s.regs with rax := .ofBitVec next} ∧
      t.data.dmem=s.dmem.storeInt (next+8) 8 s.regs.r12.toBitVec.toInt ∧ t.pc=codeEntry+0x5e) := by
  simp [run,IndexMutatorImage.Replace.r56,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Replace.entry] at read mapped ⊢
  rw [read]
  simp only [Effects.All]
  rw [←BitVec.toInt_eq_toNat_bmod next,BitVec.ofInt_toInt,mapped]
  simp [Effects.All,BitVec.ofInt_natCast]

def clearedMemory (s : MachineData) : DataMem :=
  ((s.dmem.storeInt (s.regs.rbx.toBitVec+8) 8 0).storeInt
    (s.regs.rbx.toBitVec+16) 8 (0xdead000000000122 : BitVec 64).toInt).storeInt
    (s.regs.rbx.toBitVec+16) 8 0

theorem clear_stores (s : MachineData) (oldNext oldBack : Int)
    (mappedNext : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some oldNext)
    (mappedBack : (s.dmem.storeInt (s.regs.rbx.toBitVec+8) 8 0).loadInt (s.regs.rbx.toBitVec+16) 8=some oldBack) :
    (run IndexMutatorImage.Replace.r63 0x63 s).All (fun t =>
      t.data.regs={s.regs with rax := 0xdead000000000122} ∧
      t.data.dmem=clearedMemory s ∧ t.pc=codeEntry+0x81) := by
  have last := load64_store (s.dmem.storeInt (s.regs.rbx.toBitVec+8) 8 0)
    (s.regs.rbx.toBitVec+16) (0xdead000000000122 : BitVec 64)
  simp [run,IndexMutatorImage.Replace.r63,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Replace.entry,clearedMemory] at mappedNext mappedBack last ⊢
  rw [mappedNext]
  simp only [Effects.All]
  rw [mappedBack]
  simp only [Effects.All]
  rw [last]
  simp only [Effects.All]
  decide +kernel

#print axioms successor_store
#print axioms clear_stores
end Binary.Pair.Replace
