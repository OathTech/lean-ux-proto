import AllowedipsMutationCodeLayout
import StackFrame

namespace Binary.Pair.Allowedips
local instance : Labels := Image.linkedLabels

def incrementCode := AllowedipsMutationImage.Insert4.r1a.take 1

theorem increment_layout4 : LaidOut AllowedipsMutationImage.Insert4.fetch
    (AllowedipsMutationImage.Insert4.entry+0x1a) incrementCode := by binary_layout

theorem increment_layout6 : LaidOut AllowedipsMutationImage.Insert6.fetch
    (AllowedipsMutationImage.Insert6.entry+0x25) incrementCode := by binary_layout

/-- The actual u64 increment, including wraparound. This physical lemma does
not assume a non-wrapping mirror counter. The mirror correction is separate. -/
theorem increment_region (s : MachineData) (pc : Int64) (old : BitVec 64)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old.toNat) :
    (Directives.interp incrementCode s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.pc=pc+5 ∧ t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+16) 8 (1+old).toInt) := by
  simp [incrementCode,AllowedipsMutationImage.Insert4.r1a,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,MachineData.load,MachineData.store,MachineData.set,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_ofNat,
    BitVec.ofInt_toInt,Effects.All] at read ⊢
  rw [read]
  simp [Effects.All,BitVec.toInt_eq_toNat_bmod]

theorem increment_effect (fetch : Int64 → Option Decoded) (pc : Int64)
    (layout : LaidOut fetch pc incrementCode) (s : MachineData) (old : BitVec 64)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ t.data.regs=s.regs ∧
      t.data.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some ((1+old).toNat : Int) ∧
      EqualOutside (InRange (s.regs.rbx.toBitVec+16) 8) s.dmem t.data.dmem) ⟨s,pc⟩ := by
  have run := region_eventually layout s _ (increment_region s pc old read)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨position,registers,memory⟩
  refine ⟨position,registers,?_,?_⟩
  · rw [memory]
    exact load64_store _ _ _
  · rw [memory]
    exact storeInt_frame _ _ _ _

#print axioms increment_effect
end Binary.Pair.Allowedips
