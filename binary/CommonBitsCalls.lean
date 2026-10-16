import CommonBitsCoverage
import CommonBitsStack
import CallComposition

namespace Binary.CommonBitsCoverage
open TrustBase Instrumentation
local instance : Labels := Image.linkedLabels

structure CallsReady (c : Context) (s : MachineData) : Prop where
  state : c.At s.dmem
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true
  pushSeparate : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  returnSeparate : ∀ a, c.writes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  metadataSeparate : ∀ a, c.writes a → ¬c.metadataBytes a
  preemptSeparate : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a

theorem CallsReady.congr {c : Context} {before after : MachineData}
    (ready : CallsReady c before) (memory : after.dmem = before.dmem)
    (stack : after.regs.rsp = before.regs.rsp) : CallsReady c after := by
  exact {
    state := by simpa only [memory] using ready.state
    aligned := by simpa only [stack] using ready.aligned
    mapped := by simpa only [memory, stack] using ready.mapped
    pushSeparate := by simpa only [stack] using ready.pushSeparate
    returnSeparate := by simpa only [stack] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

theorem called_ready (c : Context) (s : MachineData) (returnPC target : Int64)
    (ready : CallsReady c s) :
    EntryFrame (calledState s returnPC target) returnPC.toUInt64 ∧
    c.At (calledState s returnPC target).data.dmem := by
  constructor
  · exact Instrumentation.called_entry s returnPC target ready.aligned
  · exact state_frame c _ _ ready.state _
      (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt) ready.pushSeparate

/-- The actual CALL followed by its named callback contract, with the same
    full fetch and physical state. The returned state is ready for another call. -/
theorem call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (s : MachineData) (history : List MachineState)
    (ready : CallsReady c s) :
    Eventually (historyStep fetch) (fun t =>
      Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
      CallsReady c t.machine.data ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a)
        s.dmem t.machine.data.dmem ∧
      ∃ localHistory, t.history = history ++ localHistory ∧
        NoAnchoredReentry localHistory ∧ NoAllowedipsReentry localHistory)
      ⟨⟨s, pc⟩, history⟩ := by
  have entry := called_ready c s (pc+5) (label target) ready
  have service := callback fetch (label target) kind contract c
    (calledState s (pc+5) (label target)) (pc+5).toUInt64 rfl entry.1 entry.2
    (by simpa [calledState] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate
  have joined := history_prepend fetch _ _ service history
  let recordedHistory (t : Executed) : Prop := ∃ localHistory,
    t.history = history ++ localHistory ∧ NoAnchoredReentry localHistory ∧ NoAllowedipsReentry localHistory
  have run := call_return fetch pc target here s history c.writes c.At recordedHistory
    ready.mapped ready.returnSeparate (by
      apply eventually_weaken (historyStep fetch) _ _ _ _ joined
      rintro final ⟨localState, ⟨returned, state, frame, noReentry, noAllowedips⟩, machine, recorded⟩
      exact ⟨machine.symm ▸ returned, machine.symm ▸ state, machine.symm ▸ frame,
        localState.history, recorded, noReentry, noAllowedips⟩)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, state, sp, mapped, frame, recorded⟩
  refine ⟨returned, ?_, frame, recorded⟩
  exact {
    state := state
    aligned := by simpa only [sp] using ready.aligned
    mapped := mapped
    pushSeparate := by simpa only [sp] using ready.pushSeparate
    returnSeparate := by simpa only [sp] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

/-- A proved region ending at a real callback entry can be composed with that
    callback. The execution premise is discharged by a named region theorem;
    this lemma introduces no service readiness or preservation assumption. -/
theorem region_callback (fetch : Int64 → Option Decoded) (address returnPC : Int64)
    (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch address
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (initial : MachineState) (s : MachineData) (registers : Reg64s)
    (ready : CallsReady c s)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {registers with rsp := s.regs.rsp-8} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt ∧
      t.pc = address) initial) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = returnPC ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbx = registers.rbx ∧ t.data.regs.rbp = registers.rbp ∧
      t.data.regs.r12 = registers.r12 ∧ t.data.regs.r13 = registers.r13 ∧
      t.data.regs.r14 = registers.r14 ∧ t.data.regs.r15 = registers.r15 ∧
      CallsReady c t.data ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a)
        s.dmem t.data.dmem) initial := by
  apply eventually_trans (instructionStep fetch) _ _ _ region
  rintro entered ⟨registersEq, memoryEq, pcEq⟩
  have template := called_ready c s returnPC address ready
  have entry : EntryFrame entered returnPC.toUInt64 := by
    simpa only [EntryFrame, registersEq, memoryEq, calledState] using template.1
  have state : c.At entered.data.dmem := by
    simpa only [memoryEq, calledState] using template.2
  have service := callback fetch address kind contract c entered returnPC.toUInt64
    pcEq entry state (by simpa [registersEq] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate
  have machineRun := history_project fetch _ _ service
  apply eventually_weaken (instructionStep fetch) _ _ _ _ machineRun
  rintro final ⟨history, returned, state, frame, _, _⟩
  have sp : final.data.regs.rsp = s.regs.rsp := by
    rw [returned.2.1, registersEq]
    apply UInt64.toBitVec_inj.mp
    change (s.regs.rsp.toBitVec-8)+8 = s.regs.rsp.toBitVec
    exact BitVec.sub_add_cancel _ _
  have word : final.data.dmem.loadInt (s.regs.rsp.toBitVec-8) 8 =
      some (returnPC.toBitVec.toNat : Int) := by
    have same := frame.loadInt (s.regs.rsp.toBitVec-8) 8 (by
      intro byte bound written
      exact ready.returnSeparate _ written ⟨byte, bound, rfl⟩)
    rw [memoryEq] at same
    exact same.symm.trans (load64_store s.dmem (s.regs.rsp.toBitVec-8) returnPC.toBitVec)
  have nextReady : CallsReady c final.data := {
    state := state
    aligned := by simpa only [sp] using ready.aligned
    mapped := by rw [sp, word]; rfl
    pushSeparate := by simpa only [sp] using ready.pushSeparate
    returnSeparate := by simpa only [sp] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }
  refine ⟨returned.1, sp, ?_, ?_, ?_, ?_, ?_, ?_, nextReady, ?_⟩
  · simpa only [registersEq] using returned.2.2.1
  · simpa only [registersEq] using returned.2.2.2.1
  · simpa only [registersEq] using returned.2.2.2.2.1
  · simpa only [registersEq] using returned.2.2.2.2.2.1
  · simpa only [registersEq] using returned.2.2.2.2.2.2.1
  · simpa only [registersEq] using returned.2.2.2.2.2.2.2
  · rw [memoryEq] at frame
    exact (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt).trans frame

end Binary.CommonBitsCoverage
