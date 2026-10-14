import Execution

namespace Binary

/-- The history is extended only by an actual instruction successor. Starting
    from `[initial]` records every state, including repeated PCs. -/
structure Executed where
  machine : MachineState
  history : List MachineState

def historyStep [Labels] (fetch : Int64 → Option Decoded)
    (s : Executed) (post : Executed → Prop) : Prop :=
  instructionStep fetch s.machine fun next =>
    post ⟨next, s.history ++ [next]⟩

theorem instruction_mono [Labels] (fetch : Int64 → Option Decoded)
    (s : MachineState) (P Q : MachineState → Prop)
    (h : ∀ t, P t → Q t) : instructionStep fetch s P → instructionStep fetch s Q := by
  unfold instructionStep
  split
  · exact False.elim
  · exact fun hp => ⟨hp.1, all_mono _ P Q h hp.2⟩

/-- Forgetting the automatically recorded history preserves Kraken execution,
    with the same universal treatment of undefined instruction results. -/
theorem history_project [Labels] (fetch : Int64 → Option Decoded)
    (Q : Executed → Prop) (s : Executed)
    (run : Eventually (historyStep fetch) Q s) :
    Eventually (instructionStep fetch)
      (fun t => ∃ h, Q ⟨t, h⟩) s.machine := by
  induction run with
  | done initial h => exact .done _ ⟨initial.history, h⟩
  | step initial mid ht _ ih =>
    apply step_cps
    exact instruction_mono fetch initial.machine _ _
      (fun t h => ih ⟨t, initial.history ++ [t]⟩ h) ht

/-- Lift an endpoint proof without changing its machine semantics. This does
    not establish any assertion about correspondence points; that must be
    proved from the actual history, not supplied as a ghost sequence. -/
theorem history_lift [Labels] (fetch : Int64 → Option Decoded)
    (P : MachineState → Prop) (s : MachineState)
    (run : Eventually (instructionStep fetch) P s) :
    ∀ history, Eventually (historyStep fetch) (fun t => P t.machine) ⟨s, history⟩ := by
  induction run with
  | done initial h => exact fun history => .done _ h
  | step initial mid ht _ ih =>
    intro history
    apply step_cps
    exact instruction_mono fetch initial _ _
      (fun t h => ih t h (history ++ [t])) ht

/-- Deterministic observation of every executed edge. An observation failure
    remains an error; no edge or duplicate visit is silently discarded. -/
def observeHistory {Error Checkpoint : Type}
    (edge : MachineState → MachineState → Except Error (List Checkpoint)) :
    List MachineState → Except Error (List Checkpoint)
  | [] | [_] => .ok []
  | s :: t :: rest => do
    let here ← edge s t
    let later ← observeHistory edge (t :: rest)
    return here ++ later

/-- Generic full-run transport. `MirrorRun` is the complete accepted run,
    including its worlds and events; `Matches` must equate its observations
    to the deterministic observation of the recorded machine history.
    This implication proves no function-specific simulation by itself. -/
theorem transport_run [Labels] {MirrorRun : Type}
    (fetch : Int64 → Option Decoded) (accepted : MirrorRun → Prop)
    (Matches : Executed → MirrorRun → Prop) (initial : MachineState)
    (simulation : Eventually (historyStep fetch)
      (fun t => ∃ run, accepted run ∧ Matches t run) ⟨initial, [initial]⟩)
    (P : MirrorRun → Prop) (property : ∀ run, accepted run → P run) :
    Eventually (historyStep fetch)
      (fun t => ∃ run, accepted run ∧ Matches t run ∧ P run) ⟨initial, [initial]⟩ := by
  apply eventually_weaken (historyStep fetch) _ _ _ _ simulation
  rintro t ⟨run, ha, hm⟩
  exact ⟨run, ha, hm, property run ha⟩

#print axioms history_project
#print axioms history_lift
#print axioms transport_run
end Binary
