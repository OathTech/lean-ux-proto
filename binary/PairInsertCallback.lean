import PairInsertState

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- Lift a proved preparation/CALL region through a coverage service once.
This is shared by cursor adjustment and both comparison-argument regions. -/
theorem Core.region_callback (fetch : Int64 → Option Decoded) (address returnPC : Int64)
    (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    {n o c initial ra p shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra p shadow s) (startPC : Int64) (registers : Reg64s)
    (owner : registers.rbp=s.regs.rbp) (table : registers.r12=s.regs.r12)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs={registers with rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt ∧
      t.pc=address) ⟨s,startPC⟩) :
    Eventually (instructionStep fetch) (fun t => t.pc=returnPC ∧ Core n o c initial ra p shadow t.data ∧
      t.data.regs.rbx=registers.rbx ∧ t.data.regs.r13=registers.r13 ∧
      t.data.regs.r14=registers.r14 ∧ t.data.regs.r15=registers.r15) ⟨s,startPC⟩ := by
  have run := Services.region_callback fetch address returnPC kind contract (p.context c)
    ⟨s,startPC⟩ s registers (core.calls facts) region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨atPc,sp,bx,bp,r12,r13,r14,r15,calls,frame⟩
  have frame' : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 a ∨
      (p.context c).writes a) s.dmem t.data.dmem := by simpa only [core.call_slot] using frame
  have mapped : (t.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8).isSome=true := by
    simpa only [sp,core.call_slot] using calls.mapped
  refine ⟨atPc,⟨sp.trans core.stack,(r12.trans table).trans core.table,(bp.trans owner).trans core.owner,
    core.memory.callback facts calls.state mapped frame',?_,?_⟩,bx,r13,r14,r15⟩
  all_goals
    have effect : EqualOutside (Index.External c initial 7) s.dmem t.data.dmem := by
      intro a outside
      apply frame' a
      rintro (stack | buffer)
      · exact outside (.inl (Stack.scratch _ 7 7 (by decide) (by decide) a stack))
      · rw [p.writes facts] at buffer
        exact outside (.inr (.inl (Index.phase_writes c p.disabled a buffer)))
  · exact core.frame.trans (Index.external_storage facts.toCallFacts.geometry effect)
  · exact Index.external_trans core.outside effect

#print axioms Core.region_callback
end Binary.Pair.Insert
