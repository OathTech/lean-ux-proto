import AllowedipsPeerObservation

namespace Binary.AllowedipsObservation
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

theorem silent_service (fetch : Int64 → Option Decoded) (rxSection : Nat)
    (Q : Executed → Prop) (s : MachineState)
    (localRun : Eventually (historyStep fetch)
      (fun t => Q t ∧ (NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history)) ⟨s, [s]⟩)
    (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (historyStep fetch)
      (fun t => ∃ localState tail, Q localState ∧
        t.machine = localState.machine ∧ localState.history = s :: tail ∧
        t.history = front ++ s :: tail ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        (NoAnchoredReentry localState.history ∧ NoAllowedipsReentry localState.history))
      ⟨s, front ++ [s]⟩ := by
  have prefixed := history_prefix fetch _ ⟨s, [s]⟩ [s] ⟨[], rfl⟩ localRun
  have joined := history_prepend fetch _ _ prefixed front
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro t ⟨localState, ⟨⟨good, noReentry⟩, tail, initialPrefix⟩, machine, history⟩
  have localHistory : localState.history = s :: tail := initialPrefix.symm
  refine ⟨localState, tail, good, machine, localHistory, ?_, ?_, noReentry⟩
  · simpa only [localHistory] using history
  · rw [history, localHistory, observeHistory_splice, observed]
    have empty := AllowedipsPeerObservation.global_history rxSection localState.history []
      (AllowedipsPeerObservation.no_reentry_observations rxSection localState.history noReentry.1 noReentry.2)
      (by intro p member; cases member)
    rw [localHistory] at empty
    rw [empty]
    exact congrArg Except.ok (List.append_nil events)



#print axioms silent_service
end Binary.AllowedipsObservation
