import PairInsertRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

def drawWord (s : MachineData) : BitVec 32 := s.regs.get (.low .rax .W32)
def drawBucketWord (s : MachineData) : BitVec 32 := drawWord s &&& 8191
def drawBucketAddress (s : MachineData) : BitVec 64 :=
  s.regs.r12.toBitVec+(drawBucketWord s).setWidth 64*8
def drawMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.rbp.toBitVec+28) 4 (drawWord s).toInt

private theorem of_bmod (n : Nat) :
    BitVec.ofInt 64 ((n : Int).bmod 18446744073709551616)=BitVec.ofNat 64 n := by
  simpa only [BitVec.toInt_ofNat'] using (BitVec.ofInt_toInt (x := BitVec.ofNat 64 n))

private theorem of_low32 (v : UInt64) :
    BitVec.ofNat 64 (v.toNat%4294967296%18446744073709551616)=
      (v.toBitVec.extractLsb' 0 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem u64_zero (v : UInt64) : v.toBitVec=0#64 ↔ v=0 := UInt64.toBitVec_inj

theorem draw_and_head (s : MachineData) (head : UInt64)
    (mapped : (s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4).isSome=true)
    (read : (drawMemory s).loadInt (drawBucketAddress s) 8=some head.toNat) :
    (run IndexInsertImage.Insert.r79 0x79 s).All (fun t =>
      t.data.regs={s.regs with
        rax := .ofBitVec ((drawBucketWord s).setWidth 64),
        r13 := .ofBitVec ((drawWord s).setWidth 64),rbx := head} ∧
      t.data.dmem=drawMemory s ∧
      t.pc=(if head=0 then codeEntry+0xc7 else codeEntry+0x8d)) := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp mapped
  simp [run,IndexInsertImage.Insert.r79,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    Reg64s.set,Reg64s.set64,BitVec.drop,BitVec.take,
    ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,StatusFlags.from_result,CondCode.interp,
    drawWord,drawBucketWord,drawBucketAddress,drawMemory,codeEntry,IndexInsertImage.Insert.entry] at mapped read ⊢
  simp_all [Effects.All,of_bmod,of_low32]
  by_cases zero : head=0
  all_goals simp_all [Effects.All,u64_zero]
  all_goals rfl

#print axioms draw_and_head
end Binary.Pair.Insert
