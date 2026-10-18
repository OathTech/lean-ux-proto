import PairReplaceRegions

namespace Binary.Pair.Replace
local instance : Labels := Image.linkedLabels

def copyIndex (s : MachineData) (index : BitVec 32) : DataMem :=
  s.dmem.storeInt (s.regs.rbp.toBitVec+28) 4 index.toInt
def copyNext (s : MachineData) (index : BitVec 32) (next : BitVec 64) : DataMem :=
  (copyIndex s index).storeInt (s.regs.rbp.toBitVec+8) 8 next.toInt
def copyBack (s : MachineData) (index : BitVec 32) (next previous : BitVec 64) : DataMem :=
  (copyNext s index next).storeInt (s.regs.rbp.toBitVec+16) 8 previous.toInt
def prefixMemory (s : MachineData) (index : BitVec 32) (next previous : BitVec 64) : DataMem :=
  (copyBack s index next previous).storeInt previous 8 (s.regs.rbp.toBitVec+8).toInt

theorem splice_prefix (s : MachineData) (index : BitVec 32) (next previous : BitVec 64)
    (oldIndex : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4=some index.toNat)
    (newIndex : (s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4).isSome=true)
    (oldNext : (copyIndex s index).loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat)
    (newNext : ((copyIndex s index).loadInt (s.regs.rbp.toBitVec+8) 8).isSome=true)
    (oldBack : (copyNext s index next).loadInt (s.regs.rbx.toBitVec+16) 8=some previous.toNat)
    (newBack : ((copyNext s index next).loadInt (s.regs.rbp.toBitVec+16) 8).isSome=true)
    (predecessor : ((copyBack s index next previous).loadInt previous 8).isSome=true) :
    (run IndexMutatorImage.Replace.r2b 0x2b s).All (fun t =>
      t.data.regs={s.regs with
        rax := .ofBitVec next,rdx := .ofBitVec previous,r12 := .ofBitVec (s.regs.rbp.toBitVec+8)} ∧
      t.data.dmem=prefixMemory s index next previous ∧
      t.pc=(if next=0 then codeEntry+0x5e else codeEntry+0x51)) := by
  obtain ⟨i,im⟩ := Option.isSome_iff_exists.mp newIndex
  obtain ⟨n,nm⟩ := Option.isSome_iff_exists.mp newNext
  obtain ⟨p,pm⟩ := Option.isSome_iff_exists.mp newBack
  obtain ⟨q,qm⟩ := Option.isSome_iff_exists.mp predecessor
  have back := load64_store (copyNext s index next) (s.regs.rbp.toBitVec+16) previous
  simp [run,IndexMutatorImage.Replace.r2b,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Replace.entry,copyIndex,copyNext,copyBack,prefixMemory]
    at oldIndex oldNext oldBack im nm pm qm back ⊢
  rw [oldIndex]
  simp only [Effects.All]
  rw [im]
  simp only [Effects.All]
  have index32 : (index.toNat : Int)%4294967296=index.toNat :=
    Int.emod_eq_of_lt (by omega) (by have := index.isLt; omega)
  have index64 : (index.toNat : Int)%18446744073709551616=index.toNat :=
    Int.emod_eq_of_lt (by omega) (by have := index.isLt; omega)
  rw [index32,show max (index.toNat : Int) 0=index.toNat from by omega,index64,←BitVec.toInt_eq_toNat_bmod index]
  rw [oldNext]
  simp only [Effects.All]
  rw [←BitVec.toInt_eq_toNat_bmod next,nm,oldBack]
  simp only [Effects.All]
  rw [←BitVec.toInt_eq_toNat_bmod previous,pm,back]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [←BitVec.toInt_eq_toNat_bmod previous,BitVec.ofInt_toInt]
  rw [qm]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp]
  split <;> simp_all [Effects.All]
  decide

#print axioms splice_prefix
end Binary.Pair.Replace
