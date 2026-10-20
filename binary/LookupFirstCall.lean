import GuardedCallHistory
import LookupFirstCoverage
import LookupCallHistory
import CallComposition
import LookupCoverageHistory

namespace Binary.LookupInstrumentation.First
open TrustBase LookupObservation Instrumentation Callback
local instance : Labels := Image.linkedLabels

/-- Instrumentation CALL and named service contract composed in the actual
    caller history. The callback's interior remains present and has no cuts.
    This theorem supplies no whole-World correspondence assumption. -/
theorem observed_call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩) (kind : KcovKind)
    (contract : LeafService fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (s : MachineData) (outer : UInt64) (outside : s.regs.rsp≠outer+8)
    (calleeOutside : s.regs.rsp-8≠outer+8) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt s)
    (allowed : coverage.Allowed preempt kind)
    (rxSection : Nat) (front : List MachineState) (events delta : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [⟨s, pc⟩]) = .ok events)
    (observedCall : edge rxSection ⟨s, pc⟩ (calledState s (pc+5) (label target)) = .ok delta) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
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
  have service := LookupCoverage.First.observed_callback fetch (label target) kind contract coverage preempt
    (calledState s (pc+5) (label target)) (pc+5).toUInt64 outer calleeOutside rfl entry.1 entry.2 allowed
    (by simpa [calledState, LookupCoverage.Context.Separated] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate rxSection (front ++ [⟨s, pc⟩]) (events ++ delta) afterCall
  have run := Instrumentation.First.call_return fetch pc target here s (front ++ [⟨s, pc⟩]) outer outside _ _ _
    ready.mapped ready.returnSeparate service
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ run
  rintro final ⟨returned, state, sp, mapped, frame, rest⟩
  refine ⟨returned, ?_, frame, rest⟩
  exact ready.restore state sp mapped

#print axioms called_ready
#print axioms observed_call
end Binary.LookupInstrumentation.First
