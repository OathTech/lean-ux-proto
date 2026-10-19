import PairInsertRegions
import PairInsertCallMemory
import PairIndexExternal

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- The binary-side invariant common to all insertion correspondence points.
The shadow heap changes only at the combined unlink/draw/prepend effects. -/
structure Core (n : Names) (o : Offsets) (c : Context) (initial : MachineState) (ra : UInt64) (p : Phase)
    (shadow : DataMem) (s : MachineData) : Prop where
  stack : s.regs.rsp=initial.data.regs.rsp-48
  table : s.regs.r12=initial.data.regs.rdi
  owner : s.regs.rbp=initial.data.regs.rsi
  memory : MemoryReady c initial ra (savedWords initial.data) p s.dmem
  frame : Index.StorageFrame n o shadow s.dmem
  outside : EqualOutside (Index.External c initial 7) shadow s.dmem

theorem Core.call_slot {n o c initial ra p shadow s} (core : Core n o c initial ra p shadow s) :
    s.regs.rsp.toBitVec-8=Stack.slot initial.data.regs.rsp.toBitVec 7 := by
  rw [core.stack,UInt64.toBitVec_sub]
  change (initial.data.regs.rsp.toBitVec-48)-8=initial.data.regs.rsp.toBitVec-56
  rw [BitVec.sub_sub]
  rfl

theorem Core.calls {n o c initial ra p shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s) :
    CallsReady (p.context c) s := by
  apply core.memory.calls_ready facts
  · rw [core.stack]
    exact aligned_sub _ 48 facts.entry.1 (by decide)
  · exact core.call_slot

theorem Core.callback (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (contract : ServiceReturns fetch (label target) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (here : fetch pc=some ⟨Instrumentation.callInstruction target,5⟩)
    {n o c initial ra p shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra p shadow s) :
    Eventually (instructionStep fetch) (fun t => t.pc=pc+5 ∧ Core n o c initial ra p shadow t.data ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.r13=s.regs.r13 ∧
      t.data.regs.r14=s.regs.r14 ∧ t.data.regs.r15=s.regs.r15) ⟨s,pc⟩ := by
  have run := Services.call fetch pc target .pc contract here (p.context c) s (core.calls facts)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨atPc,sp,bx,bp,r12,r13,r14,r15,calls,frame⟩
  have frame' : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 a ∨
      (p.context c).writes a) s.dmem t.data.dmem := by simpa only [core.call_slot] using frame
  have mapped : (t.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8).isSome=true := by
    simpa only [sp,core.call_slot] using calls.mapped
  refine ⟨atPc,⟨sp.trans core.stack,r12.trans core.table,bp.trans core.owner,
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

theorem start (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra}
    (facts : FrameFacts n o c initial ra) (pc : initial.pc=codeEntry) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+21 ∧
      Core n o c initial ra .enabled initial.data.dmem t.data) initial := by
  have layout := IndexInsertImage.Insert_r00_layout.agreement agree
  have region := region_eventually layout initial.data _ (prologue initial.data facts.stack)
  have initialEq : (⟨initial.data,codeEntry+(.ofNat 0)⟩ : MachineState)=initial := by
    change (⟨initial.data,codeEntry⟩ : MachineState)=initial
    cases initial
    exact congrArg (MachineState.mk _) pc.symm
  rw [initialEq] at region
  apply eventually_trans (instructionStep fetch) _ _ _ region
  rintro entered ⟨registers,memory,entryPc⟩
  have mem : MemoryReady c initial ra (savedWords initial.data) .enabled entered.data.dmem := by
    rw [memory,saveMemory]
    exact MemoryReady.initial facts _
  have sp : entered.data.regs.rsp.toBitVec=Stack.slot initial.data.regs.rsp.toBitVec 7 := by
    simp only [registers,UInt64.toBitVec_sub,Stack.slot]
    rfl
  have entryFrame : EntryFrame entered (codeEntry+21).toUInt64 := by
    refine ⟨?_,?_⟩
    · rw [registers]
      exact aligned_sub _ 56 facts.entry.1 (by decide)
    · rw [sp,memory,saveMemory]
      exact Stack.read _ _ _ 7 6 (by decide) (by decide)
  have state : c.At entered.data.dmem := ⟨mem.covered false,mem.preempt⟩
  have stackSeparate : ∀ a, c.writes a → ¬InRange entered.data.regs.rsp.toBitVec 8 a := by
    intro a written inside
    rw [sp] at inside
    exact facts.toCallFacts.geometry.bufferLive a ⟨.inl written.1,written.2⟩ (Stack.inside _ 7 7 (by decide) a inside)
  have service := Services.service_endpoint fetch (.ofNat 0xffffffff810f31f0) .pc trace c entered
    (codeEntry+21).toUInt64 entryPc entryFrame state stackSeparate
    (fun a written metadata => facts.toCallFacts.geometry.bufferMetadata a ⟨.inl written.1,written.2⟩
      (Index.phase_metadata c false a metadata))
    (fun a written count => facts.toCallFacts.geometry.bufferPreempt a ⟨.inl written.1,written.2⟩ count)
  apply Sequential.forget service
  rintro t ⟨returned,state,frame⟩
  have mapped : (t.machine.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8).isSome=true := by
    have same := frame.loadInt entered.data.regs.rsp.toBitVec 8 (by
      intro byte hb written
      exact stackSeparate _ written ⟨byte,hb,rfl⟩)
    rw [←sp,←same,entryFrame.2]
    rfl
  have frame' : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 a ∨
      (Phase.enabled.context c).writes a) entered.data.dmem t.machine.data.dmem := by
    intro a outside
    exact frame a (fun h => outside (.inr h))
  refine ⟨returned.1,⟨?_,?_,?_,mem.callback facts state mapped frame',?_,?_⟩⟩
  · rw [returned.2.1,registers]
    apply UInt64.toBitVec_inj.mp
    change (initial.data.regs.rsp.toBitVec-56)+8=initial.data.regs.rsp.toBitVec-48
    rw [show (56 : BitVec 64)=48+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
  · simpa only [registers] using returned.2.2.2.2.1
  · simpa only [registers] using returned.2.2.2.1
  all_goals
    first | apply Index.external_storage facts.toCallFacts.geometry | skip
    have saves := Stack.frame initial.data.dmem initial.data.regs.rsp.toBitVec (savedWords initial.data) 7 7 (by decide)
    change EqualOutside _ initial.data.dmem (saveMemory initial.data 7) at saves
    rw [←memory] at saves
    intro a outside
    exact (saves a (fun h => outside (.inl h))).trans
      (frame a (fun h => outside (.inr (.inl ⟨.inl h.1,h.2⟩))))

#print axioms Core.callback
#print axioms start
end Binary.Pair.Insert
