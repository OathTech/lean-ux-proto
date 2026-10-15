import CallHistory
import LookupCoverageHistory

namespace Binary.LookupInstrumentation
open TrustBase LookupObservation Instrumentation
local instance : Labels := Image.linkedLabels

/-- Physical readiness follows the actual push, not a per-call hypothesis
    that the service is able to run. -/
theorem called_ready (s : MachineData) (returnPC target : Int64)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt s) :
    EntryFrame (calledState s returnPC target) returnPC.toUInt64 ∧
    LookupCoverage.Context.At coverage preempt (calledState s returnPC target).data.dmem := by
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
  · exact LookupCoverage.state_frame coverage preempt _ _ ready.state _
      (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt) ready.pushSeparate

/-- Instrumentation CALL and named service contract composed in the actual
    caller history. The callback's interior remains present and has no cuts.
    This theorem supplies no whole-World correspondence assumption. -/
theorem observed_call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩) (kind : KcovKind)
    (contract : ServiceReturns fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (s : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt s)
    (allowed : coverage.Allowed preempt kind)
    (rxSection : Nat) (front : List MachineState) (events delta : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [⟨s, pc⟩]) = .ok events)
    (observedCall : edge rxSection ⟨s, pc⟩ (calledState s (pc+5) (label target)) = .ok delta) :
    Eventually (historyStep fetch) (fun t =>
      Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
      LookupCoverage.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨
        LookupCoverage.Context.writes coverage a) s.dmem t.machine.data.dmem ∧
      observeHistory (edge rxSection) t.history = .ok (events ++ delta) ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = (front ++ [⟨s, pc⟩]) ++ calledState s (pc+5) (label target) :: tail ∧
        (calledState s (pc+5) (label target) :: tail).getLast? = some t.machine ∧
        (∀ q ∈ (calledState s (pc+5) (label target) :: tail).dropLast, q.pc ∉ Image.cutPoints) ∧
        NoAnchoredReentry (calledState s (pc+5) (label target) :: tail))
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
  have service := LookupCoverage.observed_callback fetch (label target) kind contract coverage preempt
    (calledState s (pc+5) (label target)) (pc+5).toUInt64 rfl entry.1 entry.2 allowed
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
  have nextReady : LookupCoverage.CallsReady coverage preempt final.machine.data := {
    state := state
    phase := ready.phase
    aligned := by simpa only [sp] using ready.aligned
    mapped := by rw [sp, word]; rfl
    pushSeparate := by simpa only [sp] using ready.pushSeparate
    returnSeparate := by simpa only [sp] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }
  exact ⟨returned, nextReady,
    (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (pc+5).toBitVec.toInt).trans frame,
    observations, last, tail⟩

#print axioms called_ready
#print axioms observed_call
end Binary.LookupInstrumentation
