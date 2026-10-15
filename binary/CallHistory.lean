import KcovHistory
import PeerComparisons

namespace Binary.Instrumentation
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

def callInstruction (target : Label) : Instr :=
  .regular .W64 .W64 (.call (.rel (.sub (.label target) .after_current_instruction)))

def calledState (s : MachineData) (returnPC target : Int64) : MachineState :=
  let data : MachineData := {s with
    regs := {s.regs with rsp := s.regs.rsp-8}
    dmem := s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt}
  ⟨data, target⟩

/-- Execute the actual CALL and its pushed word before invoking a contract. -/
theorem call_instruction (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩)
    (s : MachineData) (history : List MachineState)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true) :
    historySteps fetch 1 (fun t =>
      t.machine = calledState s (pc+5) (label target) ∧
      t.history = history ++ [t.machine]) ⟨⟨s, pc⟩, history⟩ := by
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp mapped
  refine instruction_history fetch ⟨s, pc⟩ history
    (fun t => t = calledState s (pc+5) (label target)) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  have cancel (a b : Int64) : a+(b-a) = b := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm]
    exact BitVec.sub_add_cancel _ _
  simp [callInstruction, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Reg64s.get64, Reg64s.set64,
    Width.bytesv, Effects.All, calledState, cancel] at loaded ⊢
  rw [loaded]
  simp [Effects.All]

/-- Physical readiness follows the actual push, not a per-call hypothesis
    that the service is able to run. -/
theorem called_ready (s : MachineData) (returnPC target : Int64)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : PeerGet.CallsReady coverage preempt s) :
    EntryFrame (calledState s returnPC target) returnPC.toUInt64 ∧
    KcovState coverage preempt (calledState s returnPC target).data.dmem := by
  constructor
  · constructor
    · change (s.regs.rsp-8).toNat % 8 = 0
      simp only [UInt64.toNat_sub, show (8 : UInt64).toNat = 8 from rfl]
      have bound := s.regs.rsp.toNat_lt_size
      have aligned := ready.aligned
      omega
    · change (s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt).loadInt
        (s.regs.rsp-8).toBitVec 8 = _
      simp only [UInt64.toBitVec_sub, show (8 : UInt64).toBitVec = 8#64 from rfl]
      exact load64_store s.dmem (s.regs.rsp.toBitVec-8) returnPC.toBitVec
  · exact Kcov.state_frame coverage preempt _ _ ready.state _
      (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt) ready.pushSeparate

/-- The CALL's push and the service's RET cancel. Only the kernel ABI's
    saved registers are recovered; arguments and flags remain unconstrained. -/
theorem returned_caller (s : MachineData) (returnPC target : Int64) (t : MachineState)
    (returned : Returned (calledState s returnPC target) t returnPC.toUInt64) :
    t.pc = returnPC ∧ t.data.regs.rsp = s.regs.rsp ∧
    t.data.regs.rbx = s.regs.rbx ∧ t.data.regs.rbp = s.regs.rbp ∧
    t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
    t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 := by
  rcases returned with ⟨pc, sp, bx, bp, r12, r13, r14, r15⟩
  refine ⟨pc, ?_, bx, bp, r12, r13, r14, r15⟩
  rw [sp]
  apply UInt64.toBitVec_inj.mp
  change (s.regs.rsp.toBitVec-8)+8 = s.regs.rsp.toBitVec
  exact BitVec.sub_add_cancel _ _

#print axioms returned_caller

/-- Instrumentation CALL and named service contract composed in the actual
    caller history. The callback's interior remains present and has no cuts.
    This theorem supplies no whole-World correspondence assumption. -/
theorem observed_call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩) (kind : KcovKind)
    (contract : ServiceReturns fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : PeerGet.CallsReady coverage preempt s)
    (rxSection : Nat) (front : List MachineState) (events delta : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [⟨s, pc⟩]) = .ok events)
    (observedCall : edge rxSection ⟨s, pc⟩ (calledState s (pc+5) (label target)) = .ok delta) :
    Eventually (historyStep fetch) (fun t =>
      Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
      PeerGet.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨
        KcovBufferBytes coverage a) s.dmem t.machine.data.dmem ∧
      observeHistory (edge rxSection) t.history = .ok (events ++ delta) ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = (front ++ [⟨s, pc⟩]) ++ calledState s (pc+5) (label target) :: tail ∧
        (calledState s (pc+5) (label target) :: tail).getLast? = some t.machine ∧
        ∀ q ∈ (calledState s (pc+5) (label target) :: tail).dropLast, q.pc ∉ Image.cutPoints)
      ⟨⟨s, pc⟩, front ++ [⟨s, pc⟩]⟩ := by
  have call := historySteps_eventually fetch 1 _ _
    (call_instruction fetch pc target here s (front ++ [⟨s, pc⟩]) ready.mapped)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro t ⟨machine, recorded⟩
  have state : t = ⟨calledState s (pc+5) (label target),
      (front ++ [⟨s, pc⟩]) ++ [calledState s (pc+5) (label target)]⟩ := by
    cases t; simp_all
  rw [state]
  have afterCall := observeHistory_snoc (edge rxSection) (front ++ [⟨s, pc⟩])
    ⟨s, pc⟩ (calledState s (pc+5) (label target)) events delta (by simp) observed observedCall
  have entry := called_ready s (pc+5) (label target) coverage preempt ready
  have service := Kcov.observed_callback fetch (label target) kind contract coverage preempt
    (calledState s (pc+5) (label target)) (pc+5).toUInt64 rfl entry.1 entry.2
    (by simpa [calledState] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate rxSection (front ++ [⟨s, pc⟩]) (events ++ delta) afterCall
  apply eventually_weaken (historyStep fetch) _ _ _ _ service
  rintro final ⟨returned, state, frame, observations, last, tail⟩
  have sp : final.machine.data.regs.rsp = s.regs.rsp := by
    rw [returned.2.1]
    apply UInt64.toBitVec_inj.mp
    change (s.regs.rsp.toBitVec-8)+8 = s.regs.rsp.toBitVec
    exact BitVec.sub_add_cancel _ _
  have word : final.machine.data.dmem.loadInt (s.regs.rsp.toBitVec-8) 8 =
      some ((pc+5).toBitVec.toNat : Int) := by
    have unchanged := frame.loadInt (s.regs.rsp.toBitVec-8) 8 (by
      intro byte bound written
      exact ready.returnSeparate _ written ⟨byte, bound, rfl⟩)
    exact unchanged.symm.trans (load64_store s.dmem (s.regs.rsp.toBitVec-8) (pc+5).toBitVec)
  have nextReady : PeerGet.CallsReady coverage preempt final.machine.data := {
    state := state
    aligned := by simpa only [sp] using ready.aligned
    mapped := by rw [sp, word]; rfl
    pushSeparate := by simpa only [sp] using ready.pushSeparate
    returnSeparate := by simpa only [sp] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }
  exact ⟨returned, nextReady,
    (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (pc+5).toBitVec.toInt).trans frame,
    observations, last, tail⟩

#print axioms call_instruction
#print axioms called_ready
#print axioms observed_call
end Binary.Instrumentation
