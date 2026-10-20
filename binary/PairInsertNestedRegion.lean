import PairInsertDisable
import PairInsertDrawRegion
import PairInsertWalkRegions

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

def nestedBucketAddress (s : MachineData) (index : BitVec 32) : BitVec 64 :=
  s.regs.r12.toBitVec+(index &&& 8191).setWidth 64*8

def nestedDisable := IndexInsertImage.Insert.rd1.take 1
def nestedIndex := (IndexInsertImage.Insert.rd1.drop 1).take 2
def nestedMask := (IndexInsertImage.Insert.rd1.drop 3).take 1
def nestedHead := (IndexInsertImage.Insert.rd1.drop 4).take 1
def nestedTest := IndexInsertImage.Insert.rd1.drop 5

set_option maxRecDepth 2048 in
theorem nested_disable_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0xd1) nestedDisable := by
  binary_layout
set_option maxRecDepth 2048 in
theorem nested_index_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0xdb) nestedIndex := by
  binary_layout
set_option maxRecDepth 2048 in
theorem nested_mask_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0xe2) nestedMask := by
  binary_layout
set_option maxRecDepth 2048 in
theorem nested_head_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0xe9) nestedHead := by
  binary_layout
set_option maxRecDepth 2048 in
theorem nested_test_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0xed) nestedTest := by
  binary_layout

theorem nested_disable_region (s : MachineData) (count : BitVec 32)
    (read : s.dmem.loadInt preemptCountAddress 4=some count.toNat) :
    (run nestedDisable 0xd1 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=Remove.preemptMemory s count ∧ t.pc=codeEntry+0xdb) := by
  simp [run,nestedDisable,IndexInsertImage.Insert.rd1,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp,
    MachineData.load,MachineData.store,MachineData.set,AddrExpr.interp,ConstExpr.interp,
    Effects.All,codeEntry,IndexInsertImage.Insert.entry,preemptCountAddress,
    Remove.preemptMemory] at read ⊢
  rw [read]
  simp only [Effects.All]
  constructor
  · congr 1
    trivial
  · decide +kernel

theorem nested_index_region (s : MachineData) (index : BitVec 32)
    (read : s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4=some index.toNat) :
    (run nestedIndex 0xdb s).All (fun t =>
      t.data.regs={s.regs with r13 := .ofNat index.toNat,r14 := .ofNat index.toNat} ∧
      t.data.dmem=s.dmem ∧ t.pc=codeEntry+0xe2) := by
  simp [run,nestedIndex,IndexInsertImage.Insert.rd1,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    Reg64s.set,Reg64s.set64,BitVec.drop,BitVec.take,
    ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_add,
    BitVec.ofInt_toInt,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexInsertImage.Insert.entry] at read ⊢
  rw [read]
  simp [Effects.All]
  constructor
  all_goals
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt index.isLt]

theorem nested_mask_region (s : MachineData) (index : BitVec 32)
    (query : s.regs.r14=UInt64.ofNat index.toNat) :
    (run nestedMask 0xe2 s).All (fun t =>
      t.data.regs={s.regs with r14 := .ofBitVec ((index &&& 8191).setWidth 64)} ∧
      t.data.dmem=s.dmem ∧ t.pc=codeEntry+0xe9) := by
  simp [run,nestedMask,IndexInsertImage.Insert.rd1,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.set,MachineData.setReg,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    Reg64s.set,Reg64s.set64,BitVec.drop,BitVec.take,ConstExpr.interp,
    Effects.All,codeEntry,IndexInsertImage.Insert.entry,query]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt index.isLt]

theorem nested_head_region (s : MachineData) (head : UInt64)
    (read : s.dmem.loadInt (s.regs.r12.toBitVec+s.regs.r14.toBitVec*8) 8=some head.toNat) :
    (run nestedHead 0xe9 s).All (fun t =>
      t.data.regs={s.regs with rbx := head} ∧
      t.data.dmem=s.dmem ∧ t.pc=codeEntry+0xed) := by
  simp [run,nestedHead,IndexInsertImage.Insert.rd1,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,Reg64s.get64,
    Reg64s.set,Reg64s.set64,BitVec.take,
    ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,codeEntry,IndexInsertImage.Insert.entry] at read ⊢
  rw [read]
  simp [Effects.All]

theorem nested_test_region (s : MachineData) :
    (run nestedTest 0xed s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if s.regs.rbx.toBitVec=0 then codeEntry+0x12c else codeEntry+0xf2)) := by
  change (Directives.interp (testCode "L_ffffffff813a04cc") s (codeEntry+0xed)
    (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a04cc"=codeEntry+0x12c := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0xed : Int64)+5=0xf2 by decide +kernel]
    using guard_generic "L_ffffffff813a04cc" (codeEntry+0xed) s

#print axioms nested_disable_region
#print axioms nested_index_region
#print axioms nested_mask_region
#print axioms nested_head_region
#print axioms nested_test_region
end Binary.Pair.Insert
