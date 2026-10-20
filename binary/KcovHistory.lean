import ServiceObservation

namespace Binary.Kcov
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

/-- History-aware callback application in the caller's actual prefix.
    Interior cuts/observations are excluded by the named service contract,
    while physical readiness and preservation are proved from memory. -/
theorem observed_callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : KcovState layout preempt s.data.dmem)
    (stack : KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : KcovSeparated layout (KcovMetadataBytes layout))
    (preemptFrame : KcovSeparated layout (InRange preemptCountAddress 4))
    (rxSection : Nat) (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        KcovState layout preempt t.machine.data.dmem ∧
        EqualOutside (KcovBufferBytes layout) s.data.dmem t.machine.data.dmem ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        t.history.getLast? = some t.machine ∧
        ∃ tail, t.history = front ++ s :: tail ∧
          (s :: tail).getLast? = some t.machine ∧
          ∀ q ∈ (s :: tail).dropLast, q.pc ∉ Image.cutPoints)
      ⟨s, front ++ [s]⟩ := by
  have run := callback fetch address kind contract layout preempt s returnAddress atEntry entry
    state stack metadata preemptFrame
  have withLast := history_last fetch _ ⟨s, [s]⟩ rfl run
  let Q (t : Executed) : Prop := Returned s t.machine returnAddress ∧
    KcovState layout preempt t.machine.data.dmem ∧
    EqualOutside (KcovBufferBytes layout) s.data.dmem t.machine.data.dmem ∧
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
    tail, history, last, ?_⟩
  · rw [history, List.getLast?_append, last]
    rfl
  · intro q present
    exact no_reentry_cuts localState.history noReentry q (by simpa only [localHistory] using present)

#print axioms observed_callback
end Binary.Kcov
