import PairReplaceRegions
import PairReplacePre
import PairIndexExternal

namespace Binary.Pair.Replace
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

structure Core (c : Context) (initial : MachineState) (ra : UInt64) (disabled : Bool)
    (shadow : DataMem) (result : UInt64) (s : MachineData) : Prop where
  stack : s.regs.rsp=initial.data.regs.rsp-32
  owner : s.regs.rbx=initial.data.regs.rsi
  new : s.regs.rbp=initial.data.regs.rdx
  r13 : s.regs.r13=result
  r14 : s.regs.r14=initial.data.regs.r14
  r15 : s.regs.r15=initial.data.regs.r15
  memory : MemoryReady c initial ra 5 (savedWords initial.data) disabled s.dmem
  frame : EqualOutside (External c initial 5) shadow s.dmem

theorem Core.call_slot {c initial ra disabled shadow result s} (core : Core c initial ra disabled shadow result s) :
    s.regs.rsp.toBitVec-8=Stack.slot initial.data.regs.rsp.toBitVec 5 := by
  rw [core.stack,UInt64.toBitVec_sub]
  change (initial.data.regs.rsp.toBitVec-32)-8=initial.data.regs.rsp.toBitVec-40
  rw [BitVec.sub_sub]
  rfl

theorem Core.calls {n o c initial ra disabled shadow result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra disabled shadow result s) :
    CallsReady (phase c disabled) s := by
  apply core.memory.calls_ready facts.geometry (by decide) s
  · rw [core.stack]
    exact aligned_sub _ 32 facts.entry.1 (by decide)
  · exact core.call_slot

theorem Core.callback (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (contract : ServiceReturns fetch (label target) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (here : fetch pc=some ⟨Instrumentation.callInstruction target,5⟩)
    {n o c initial ra disabled shadow result s} (facts : CallFacts n o c initial ra 5)
    (core : Core c initial ra disabled shadow result s) :
    Eventually (instructionStep fetch) (fun t => t.pc=pc+5 ∧ Core c initial ra disabled shadow result t.data ∧
      t.data.regs.rbp=s.regs.rbp ∧ t.data.regs.r12=s.regs.r12) ⟨s,pc⟩ := by
  have run := Services.call fetch pc target .pc contract here (phase c disabled) s (core.calls facts)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨atPc,sp,bx,bp,r12,r13,r14,r15,calls,frame⟩
  have frame' : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 5) 8 a ∨
      (phase c disabled).writes a) s.dmem t.data.dmem := by simpa only [core.call_slot] using frame
  have mapped : (t.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 5) 8).isSome=true := by
    simpa only [sp,core.call_slot] using calls.mapped
  refine ⟨atPc,⟨sp.trans core.stack,bx.trans core.owner,bp.trans core.new,r13.trans core.r13,r14.trans core.r14,
    r15.trans core.r15,core.memory.callback facts.geometry (by decide) (by decide) calls.state mapped frame',?_⟩,bp,r12⟩
  apply external_trans core.frame
  intro a outside
  apply frame' a
  rintro (stack | buffer)
  · exact outside (.inl (Stack.scratch _ 5 5 (by decide) (by decide) a stack))
  · exact outside (.inr (.inl (phase_writes c disabled a buffer)))

theorem start (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra}
    (facts : CallFacts n o c initial ra 5) (pc : initial.pc=codeEntry) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+17 ∧
      Core c initial ra false initial.data.dmem initial.data.regs.r13 t.data) initial := by
  have layout := IndexMutatorImage.Replace_r00_layout.agreement agree
  have region := region_eventually layout initial.data _ (prologue initial.data facts.stack)
  have initialEq : (⟨initial.data,codeEntry+(.ofNat 0)⟩ : MachineState)=initial := by
    change (⟨initial.data,codeEntry⟩ : MachineState)=initial
    cases initial
    exact congrArg (MachineState.mk _) pc.symm
  rw [initialEq] at region
  apply eventually_trans (instructionStep fetch) _ _ _ region
  rintro entered ⟨registers,memory,entryPc⟩
  have mem : MemoryReady c initial ra 5 (savedWords initial.data) false entered.data.dmem := by
    rw [memory,saveMemory]
    exact MemoryReady.initial facts (by decide) _
  have sp : entered.data.regs.rsp.toBitVec=Stack.slot initial.data.regs.rsp.toBitVec 5 := by
    simp only [registers,UInt64.toBitVec_sub,Stack.slot]
    rfl
  have entryFrame : EntryFrame entered (codeEntry+17).toUInt64 := by
    refine ⟨?_,?_⟩
    · rw [registers]
      exact aligned_sub _ 40 facts.entry.1 (by decide)
    · rw [sp,memory,saveMemory]
      exact Stack.read _ _ _ 5 4 (by decide) (by decide)
  have state : c.At entered.data.dmem := ⟨mem.covered false,mem.preempt⟩
  have stackSeparate : ∀ a, c.writes a → ¬InRange entered.data.regs.rsp.toBitVec 8 a := by
    intro a written inside
    rw [sp] at inside
    exact facts.geometry.bufferLive a ⟨.inl written.1,written.2⟩ (Stack.inside _ 5 5 (by decide) a inside)
  have service := Services.service_endpoint fetch (.ofNat 0xffffffff810f31f0) .pc trace c entered
    (codeEntry+17).toUInt64 entryPc entryFrame state stackSeparate
    (fun a written metadata => facts.geometry.bufferMetadata a ⟨.inl written.1,written.2⟩
      (phase_metadata c false a metadata))
    (fun a written count => facts.geometry.bufferPreempt a ⟨.inl written.1,written.2⟩ count)
  apply Sequential.forget service
  rintro t ⟨returned,state,frame⟩
  have mapped : (t.machine.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 5) 8).isSome=true := by
    have same := frame.loadInt entered.data.regs.rsp.toBitVec 8 (by
      intro byte hb written
      exact stackSeparate _ written ⟨byte,hb,rfl⟩)
    rw [←sp,←same,entryFrame.2]
    rfl
  have frame' : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 5) 8 a ∨
      (phase c false).writes a) entered.data.dmem t.machine.data.dmem := by
    intro a outside
    exact frame a (fun h => outside (.inr h))
  refine ⟨returned.1,⟨?_,?_,?_,?_,?_,?_,mem.callback facts.geometry (by decide) (by decide) state mapped frame',?_⟩⟩
  · rw [returned.2.1,registers]
    apply UInt64.toBitVec_inj.mp
    change (initial.data.regs.rsp.toBitVec-40)+8=initial.data.regs.rsp.toBitVec-32
    rw [show (40 : BitVec 64)=32+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
  · simpa only [registers] using returned.2.2.1
  · simpa only [registers] using returned.2.2.2.1
  · simpa only [registers] using returned.2.2.2.2.2.1
  · simpa only [registers] using returned.2.2.2.2.2.2.1
  · simpa only [registers] using returned.2.2.2.2.2.2.2
  · have saves := Stack.frame initial.data.dmem initial.data.regs.rsp.toBitVec (savedWords initial.data) 5 5 (by decide)
    change EqualOutside _ initial.data.dmem (saveMemory initial.data 5) at saves
    rw [←memory] at saves
    intro a outside
    exact (saves a (fun h => outside (.inl h))).trans
      (frame a (fun h => outside (.inr (.inl ⟨.inl h.1,h.2⟩))))

#print axioms Core.callback
#print axioms start
end Binary.Pair.Replace
