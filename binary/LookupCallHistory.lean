import CallComposition
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
  · exact Instrumentation.called_entry s returnPC target ready.aligned
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
  have afterCall := observeHistory_snoc (edge rxSection) (front ++ [⟨s, pc⟩])
    ⟨s, pc⟩ (calledState s (pc+5) (label target)) events delta (by simp) observed observedCall
  have entry := called_ready s (pc+5) (label target) coverage preempt ready
  have service := LookupCoverage.observed_callback fetch (label target) kind contract coverage preempt
    (calledState s (pc+5) (label target)) (pc+5).toUInt64 rfl entry.1 entry.2 allowed
    (by simpa [calledState, LookupCoverage.Context.Separated] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate rxSection (front ++ [⟨s, pc⟩]) (events ++ delta) afterCall
  have run := call_return fetch pc target here s (front ++ [⟨s, pc⟩]) _ _ _
    ready.mapped ready.returnSeparate service
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, state, sp, mapped, frame, rest⟩
  refine ⟨returned, ?_, frame, rest⟩
  exact ready.restore state sp mapped

#print axioms called_ready
#print axioms observed_call
end Binary.LookupInstrumentation
