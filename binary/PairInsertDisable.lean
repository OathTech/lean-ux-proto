import PairInsertGuard

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem disable_retry_region (s : MachineData) (count : BitVec 32)
    (read : s.dmem.loadInt preemptCountAddress 4=some count.toNat) :
    (run IndexInsertImage.Insert.r65 0x65 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=Remove.preemptMemory s count ∧ t.pc=codeEntry+0x6f) := by
  simp [run,IndexInsertImage.Insert.r65,Directives.interp,Directive.interp,
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

theorem disable_retry (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .enabled shadow s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x6f ∧
      Core n o c initial ra .outer shadow t.data) ⟨s,codeEntry+0x65⟩ := by
  have frame := storeInt_frame s.dmem preemptCountAddress 4 (BitVec.ofInt 32 (512+c.preempt.toNat)).toInt
  have memory := core.memory.preempt_transition (q := .outer) facts frame (Remove.preempt_read s c.preempt)
  have physical := disable_retry_region s c.preempt (load32_raw _ _ _ core.memory.preempt)
  have run := region_eventually (IndexInsertImage.Insert_r65_layout.agreement decoder) s _ physical
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨registers,heap,pc⟩
  refine ⟨pc,⟨by simpa only [registers] using core.stack,
    by simpa only [registers] using core.table,by simpa only [registers] using core.owner,
    by simpa [heap,Remove.preemptMemory,Int.natCast_add] using memory,?_,?_⟩⟩
  all_goals
    have effect : EqualOutside (External c initial 7) s.dmem t.data.dmem := by
      rw [heap]
      exact fun a outside => frame a (fun inside => outside (.inr (.inr inside)))
  · exact core.frame.trans (external_storage facts.toCallFacts.geometry effect)
  · exact external_trans core.outside effect

#print axioms disable_retry_region
#print axioms disable_retry
end Binary.Pair.Insert
