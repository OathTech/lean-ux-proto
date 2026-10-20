import CommonBitsCalls
import SequentialExecution

namespace Binary.Pair.Services
open TrustBase Instrumentation CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- Conditional callback readiness and its exact stores, using the existing
named service contract. No M2-specific history exclusion is required. -/
theorem service_endpoint (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : c.At s.data.dmem)
    (stack : ∀ a, c.writes a → ¬InRange s.data.regs.rsp.toBitVec 8 a)
    (metadata : ∀ a, c.writes a → ¬c.metadataBytes a)
    (preemptFrame : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        c.At t.machine.data.dmem ∧
        EqualOutside c.writes s.data.dmem t.machine.data.dmem) ⟨s, [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnAddress.toBitVec := by
    simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have run := contract s returnAddress atEntry
    (ready c kind s returnAddress.toBitVec state returnRead stack) entry
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned, frame, effect, _⟩
  have preserved := state_preserved c kind s t.machine returnAddress.toBitVec
    state returnRead metadata preemptFrame effect frame
  exact ⟨returned, preserved.1, preserved.2⟩

theorem region_callback (fetch : Int64 → Option Decoded) (address returnPC : Int64)
    (kind : KcovKind)
    (contract : ServiceReturns fetch address
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
  have service := service_endpoint fetch address kind contract c entered returnPC.toUInt64
    pcEq entry state (by simpa [registersEq] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate
  have machineRun := history_project fetch _ _ service
  apply eventually_weaken (instructionStep fetch) _ _ _ _ machineRun
  rintro final ⟨history, returned, state, frame⟩
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

theorem call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (kind : KcovKind)
    (contract : ServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (here : fetch pc=some ⟨callInstruction target,5⟩)
    (c : Context) (s : MachineData) (ready : CallsReady c s) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ t.data.regs.rsp=s.regs.rsp ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.rbp=s.regs.rbp ∧
      t.data.regs.r12=s.regs.r12 ∧ t.data.regs.r13=s.regs.r13 ∧
      t.data.regs.r14=s.regs.r14 ∧ t.data.regs.r15=s.regs.r15 ∧
      CallsReady c t.data ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a)
        s.dmem t.data.dmem) ⟨s,pc⟩ := by
  apply region_callback fetch (label target) (pc+5) kind contract c ⟨s,pc⟩ s s.regs ready
  apply Sequential.forget
    (historySteps_eventually fetch _ _ _ (call_instruction fetch pc target here s [] ready.mapped))
  rintro t ⟨machine,_⟩
  simp [machine,calledState]

#print axioms service_endpoint
#print axioms region_callback
#print axioms call
end Binary.Pair.Services
