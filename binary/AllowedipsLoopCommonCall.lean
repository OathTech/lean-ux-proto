import AllowedipsLoopCommon
import CommonBitsCallerState

namespace Binary.AllowedipsLoop
open TrustBase Instrumentation LookupObservation
local instance : Labels := Image.linkedLabels

/-- Join the actual helper history to the caller prefix. Caller readiness
comes from the physically preserved return word and returned coverage state. -/
theorem common_call (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contracts : CommonBits.Callbacks fetch) (base s : MachineData)
    (i : CommonBits.Input) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s)
    (caller : CommonBits.CallerAt i coverage s)
    (rxSection : Nat) (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xe5⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = AllowedipsImage.Lookup.entry+0xea ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      t.machine.data.regs.r14 = s.regs.r14 ∧ t.machine.data.regs.r15 = s.regs.r15 ∧
      (t.machine.data.regs.get (.low .rax .W8)).toNat = i.result ∧
      ∃ delta, delta.map CommonBits.pointView = ((.call "common_bits",none)::i.signature rxSection) ∧
        Trace base coverage rxSection history (events ++ delta) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xe5⟩,history⟩ := by
  have entry := caller.entry
  have returnTarget := caller.returnTarget
  have run := common_local fetch agree contracts s i coverage frame.ready.mapped entry returnTarget rxSection
  have joined := history_prepend fetch _ _ run history.dropLast
  rw [history_restore last] at joined
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro final ⟨localState,⟨post,trace⟩,machine,recorded⟩
  have sp : localState.machine.data.regs.rsp = s.regs.rsp := by
    rw [post.stack,entry.stack]
    change (s.regs.rsp-8)-32+40 = s.regs.rsp
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add,UInt64.toBitVec_sub]
    change (s.regs.rsp.toBitVec-8)-32+40 = s.regs.rsp.toBitVec
    rw [BitVec.sub_sub]
    exact BitVec.sub_add_cancel _ _
  have r12 : localState.machine.data.regs.r12 = s.regs.r12 := post.r12.trans entry.savedR12
  have r13 : localState.machine.data.regs.r13 = s.regs.r13 := post.r13.trans entry.savedR13
  have returnRead := (entry.body.reads.frame post.frame entry.bodySeparate)
    ⟨i.stack.toBitVec+32,8,i.returnAddress.toNat⟩ (by simp [CommonBits.Input.words])
  have returnAddress : i.stack.toBitVec+32 = s.regs.rsp.toBitVec-8 := by
    rw [entry.stack]
    change ((s.regs.rsp-8)-32).toBitVec+32 = s.regs.rsp.toBitVec-8
    simp only [UInt64.toBitVec_sub]
    exact BitVec.sub_add_cancel _ _
  have ready : CommonBitsCoverage.CallsReady coverage localState.machine.data := {
    state := post.coverage
    aligned := by rw [sp]; exact frame.ready.aligned
    mapped := by rw [sp,←returnAddress,returnRead]; rfl
    pushSeparate := by rw [sp]; exact frame.ready.pushSeparate
    returnSeparate := by rw [sp]; exact frame.ready.returnSeparate
    metadataSeparate := frame.ready.metadataSeparate
    preemptSeparate := frame.ready.preemptSeparate }
  have widen {memory : Mem 64}
      (small : EqualOutside (writes s.regs.rsp coverage) s.dmem memory) :
      EqualOutside (writes base.regs.rsp coverage) base.dmem memory := by
    rw [frame.stack] at small
    intro a outside
    exact (frame.memory a outside).trans (small a outside)
  have nextFrame : Frame base coverage final.machine.data := by
    rw [machine]
    refine ⟨ready,sp.trans frame.stack,r12.trans frame.width,r13.trans frame.family,
      widen trace.frame,?_,frame.coverageSeparate⟩
    rw [←frame.stack]
    exact caller.finalMapped post
  obtain ⟨delta,localObserved,signature⟩ := trace.observed
  have localTrace := Trace.of_path observed last localState.history trace.head recorded
    (by rw [machine]; exact trace.last) nextFrame delta localObserved
    (fun q member cut => widen (trace.cuts q member cut)) trace.ordinary
  refine ⟨?_,?_,?_,?_,?_,?_,delta,signature,localTrace⟩
  · rw [machine,post.pc,returnTarget]
  · rw [machine,post.rbx]; exact entry.savedBx
  · rw [machine,post.rbp]; exact entry.savedBp
  · rw [machine,post.r14]; rfl
  · rw [machine,post.r15]; rfl
  · rw [machine]; exact post.result

#print axioms common_call
end Binary.AllowedipsLoop
