import ServiceObservation
import LookupCoverageCalls

namespace Binary.LookupCoverage
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

/-- History-aware callback application in the caller's actual prefix.
    Interior cuts/observations are excluded by the named service contract,
    while physical readiness and preservation are proved from memory. -/
theorem observed_callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (layout : Context) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : Context.At layout preempt s.data.dmem)
    (allowed : layout.Allowed preempt kind)
    (stack : Context.Separated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : Context.Separated layout (Context.metadataBytes layout))
    (preemptFrame : Context.Separated layout (InRange preemptCountAddress 4))
    (rxSection : Nat) (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        Context.At layout preempt t.machine.data.dmem ∧
        EqualOutside (Context.writes layout) s.data.dmem t.machine.data.dmem ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        t.history.getLast? = some t.machine ∧
        ∃ tail, t.history = front ++ s :: tail ∧
          (s :: tail).getLast? = some t.machine ∧
          (∀ q ∈ (s :: tail).dropLast, q.pc ∉ Image.cutPoints) ∧
          NoAnchoredReentry (s :: tail))
      ⟨s, front ++ [s]⟩ := by
  have run := callback fetch address kind contract layout preempt s returnAddress atEntry entry
    state allowed stack metadata preemptFrame
  have withLast := history_last fetch _ ⟨s, [s]⟩ rfl run
  let Q (t : Executed) : Prop := Returned s t.machine returnAddress ∧
    Context.At layout preempt t.machine.data.dmem ∧
    EqualOutside (Context.writes layout) s.data.dmem t.machine.data.dmem ∧
    t.history.getLast? = some t.machine
  have localRun : Eventually (historyStep fetch) (fun t => Q t ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ withLast
    rintro t ⟨⟨returned, state, frame, noReentry⟩, last⟩
    exact ⟨⟨returned, state, frame, last⟩, noReentry⟩
  have joined := silent_service fetch rxSection Q s localRun front events observed
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro t ⟨localState, tail, ⟨returned, state, frame, last⟩, machine,
    localHistory, history, observed, noReentry⟩
  rw [localHistory, ← machine] at last
  refine ⟨machine ▸ returned, machine ▸ state, machine ▸ frame, observed, ?_,
    tail, history, last, ?_, ?_⟩
  · rw [history, List.getLast?_append, last]
    rfl
  · intro q present
    exact no_reentry_cuts localState.history noReentry q (by simpa only [localHistory] using present)

  · simpa only [localHistory] using noReentry

#print axioms observed_callback
end Binary.LookupCoverage
