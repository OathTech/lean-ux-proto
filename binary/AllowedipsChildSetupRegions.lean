import PairAllowedipsChildSetup
import AllowedipsRootStore

namespace Binary.Pair.Allowedips.ChildSetup
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem entry_step (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8).isSome=true) :
    (Placement.physical Add.r1ff 0x1ff s).All (fun t =>
      t.pc=(if s.regs.rbx==0 then Add.entry+0x601 else Add.entry+0x20d) ∧
      t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+24) 8 s.regs.r8.toBitVec.toInt) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have target : (label "L_ffffffff813a11c1" : Int64)=Add.entry+0x601 := by decide +kernel
  simp [Placement.physical,Add.r1ff,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,StatusFlags.from_result,
    CondCode.interp,target] at read ⊢
  rw [read]
  simp only [Effects.All]
  intro _
  have zero : s.regs.rbx.toBitVec=0#64 ↔ s.regs.rbx=0 := UInt64.toBitVec_inj
  simp only [zero]
  by_cases empty : s.regs.rbx=0 <;> simp only [empty,ite_true,ite_false,Effects.All]
  all_goals simp only [and_true]
  all_goals rfl

theorem save_step (s : MachineData) (first second : DataMem)
    (mapped0 : (s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8).isSome=true)
    (firstEq : first=s.dmem.storeInt (s.regs.rsp.toBitVec+16) 8 s.regs.rax.toBitVec.toInt)
    (mapped1 : (first.loadInt (s.regs.rsp.toBitVec+8) 1).isSome=true)
    (secondEq : second=first.storeInt (s.regs.rsp.toBitVec+8) 1 (s.regs.get (.low .rdx .W8)).toInt)
    (mapped2 : (second.loadInt s.regs.rsp.toBitVec 8).isSome=true) :
    (Placement.physical (Add.r6e0.take 3) 0x6e0 s).All (fun t =>
      t.pc=Add.entry+0x6ed ∧ t.data.regs=s.regs ∧
      t.data.dmem=second.storeInt s.regs.rsp.toBitVec 8 s.regs.r8.toBitVec.toInt) := by
  obtain ⟨old0,read0⟩ := Option.isSome_iff_exists.mp mapped0
  obtain ⟨old1,read1⟩ := Option.isSome_iff_exists.mp mapped1
  obtain ⟨old2,read2⟩ := Option.isSome_iff_exists.mp mapped2
  subst second first
  simp [Placement.physical,Add.r6e0,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at read0 read1 read2 ⊢
  rw [read0]
  simp only [Effects.All]
  rw [read1]
  simp only [Effects.All]
  rw [read2]
  simp [Effects.All,Add.entry]

#print axioms entry_step
#print axioms save_step
end Binary.Pair.Allowedips.ChildSetup
