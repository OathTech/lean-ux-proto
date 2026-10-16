import Execution

namespace Binary

/-- A recorded endpoint recovers the complete history from its proper prefix. -/
theorem history_restore {α : Type u} {history : List α} {last : α}
    (ends : history.getLast? = some last) : history.dropLast ++ [last] = history := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp ends
  simp

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

/-- A finite unrolling of the actual fetched-instruction judgment. The count
    is a proof device for one region, never a replacement transition system. -/
def historySteps [Labels] (fetch : Int64 → Option Decoded) :
    Nat → (Executed → Prop) → Executed → Prop
  | 0, post, s => post s
  | n + 1, post, s => historyStep fetch s (historySteps fetch n post)

/-- A single instruction has exactly one appended successor, even when its
    effects universally quantify undefined flags. -/
theorem instruction_history [Labels] (fetch : Int64 → Option Decoded)
    (s : MachineState) (history : List MachineState) (P : MachineState → Prop)
    (run : instructionStep fetch s P) :
    historySteps fetch 1
      (fun t => P t.machine ∧ t.history = history ++ [t.machine]) ⟨s, history⟩ :=
  instruction_mono fetch s _ _ (fun _ h => ⟨h, rfl⟩) run

theorem historySteps_mono [Labels] (fetch : Int64 → Option Decoded)
    (n : Nat) (P Q : Executed → Prop) (h : ∀ t, P t → Q t) (s : Executed) :
    historySteps fetch n P s → historySteps fetch n Q s := by
  induction n generalizing s with
  | zero => exact h s
  | succ n ih =>
    exact instruction_mono fetch s.machine _ _ (fun t => ih ⟨t, s.history ++ [t]⟩)

theorem historySteps_eventually [Labels] (fetch : Int64 → Option Decoded)
    (n : Nat) (P : Executed → Prop) (s : Executed)
    (run : historySteps fetch n P s) : Eventually (historyStep fetch) P s := by
  induction n generalizing s with
  | zero => exact .done s run
  | succ n ih =>
    apply step_cps
    exact instruction_mono fetch s.machine _ _ (fun t ht => ih ⟨t, s.history ++ [t]⟩ ht) run

theorem historySteps_add [Labels] (fetch : Int64 → Option Decoded)
    (n m : Nat) (P : Executed → Prop) (s : Executed) :
    historySteps fetch (n + m) P s =
      historySteps fetch n (historySteps fetch m P) s := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, historySteps]
  | succ n ih =>
    simp only [Nat.succ_add, historySteps, historyStep]
    congr 1
    funext t
    exact ih ⟨t, s.history ++ [t]⟩

#print axioms historySteps_eventually
#print axioms historySteps_add

/-- A locally proved callee execution can be inserted into its caller's
    actual history. Every local state remains present and in order. -/
theorem history_prepend [Labels] (fetch : Int64 → Option Decoded)
    (Q : Executed → Prop) (s : Executed)
    (run : Eventually (historyStep fetch) Q s) (front : List MachineState) :
    Eventually (historyStep fetch)
      (fun t => ∃ localState, Q localState ∧ t.machine = localState.machine ∧
        t.history = front ++ localState.history)
      ⟨s.machine, front ++ s.history⟩ := by
  induction run with
  | done initial h => exact .done _ ⟨initial, h, rfl, rfl⟩
  | step initial mid ht _ ih =>
    apply step_cps
    apply instruction_mono fetch initial.machine _ _ _ ht
    intro next hn
    simpa only [List.append_assoc] using ih ⟨next, initial.history ++ [next]⟩ hn

#print axioms history_prepend

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

/-- Join two actual histories at their shared state, counting each edge
    once. Observation errors propagate through either half. -/
theorem observeHistory_splice {Error Checkpoint : Type}
    (edge : MachineState → MachineState → Except Error (List Checkpoint))
    (front : List MachineState) (shared : MachineState) (back : List MachineState) :
    observeHistory edge (front ++ shared :: back) = (do
      let first ← observeHistory edge (front ++ [shared])
      let second ← observeHistory edge (shared :: back)
      pure (first ++ second)) := by
  induction front with
  | nil =>
    change observeHistory edge (shared :: back) = (do
      let first ← Except.ok []
      let second ← observeHistory edge (shared :: back)
      pure (first ++ second))
    cases observeHistory edge (shared :: back) <;> rfl
  | cons s front ih =>
    cases front with
    | nil =>
      simp only [List.cons_append, List.nil_append, observeHistory]
      cases edge s shared <;> cases observeHistory edge (shared :: back) <;>
        first | rfl | exact congrArg Except.ok (by simp : _ = _)
    | cons t front =>
      simp only [List.cons_append] at ih ⊢
      change (do
        let here ← edge s t
        let later ← observeHistory edge (t :: (front ++ shared :: back))
        pure (here ++ later)) = (do
        let first ← (do
          let here ← edge s t
          let later ← observeHistory edge (t :: (front ++ [shared]))
          pure (here ++ later))
        let second ← observeHistory edge (shared :: back)
        pure (first ++ second))
      rw [ih]
      cases edge s t <;> cases observeHistory edge (t :: (front ++ [shared])) <;>
        cases observeHistory edge (shared :: back) <;>
        first | rfl | exact congrArg Except.ok (List.append_assoc _ _ _).symm

#print axioms observeHistory_splice

/-- A successful full observation cannot hide an earlier observation error
    or change an already emitted prefix. This supports stuttering-cut facts
    against the fixed complete source run. -/
theorem observeHistory_prefix {Error Checkpoint : Type}
    (edge : MachineState → MachineState → Except Error (List Checkpoint))
    (front rest : List MachineState) (all : List Checkpoint)
    (observed : observeHistory edge (front ++ rest) = .ok all) :
    ∃ events suffix, observeHistory edge front = .ok events ∧ all = events ++ suffix := by
  induction front generalizing all with
  | nil => exact ⟨[], all, rfl, rfl⟩
  | cons s front ih =>
    cases front with
    | nil => exact ⟨[], all, rfl, rfl⟩
    | cons t front =>
      change (do
        let here ← edge s t
        let later ← observeHistory edge ((t :: front) ++ rest)
        pure (here ++ later)) = .ok all at observed
      cases he : edge s t with
      | error e => rw [he] at observed; cases observed
      | ok here =>
        cases hl : observeHistory edge ((t :: front) ++ rest) with
        | error e => rw [he, hl] at observed; cases observed
        | ok later =>
          rw [he, hl] at observed
          have hall : here ++ later = all := Except.ok.inj observed
          obtain ⟨events, suffix, hp, hs⟩ := ih later hl
          refine ⟨here ++ events, suffix, ?_, ?_⟩
          · change (do
              let first ← edge s t
              let next ← observeHistory edge (t :: front)
              pure (first ++ next)) = .ok (here ++ events)
            rw [he, hp]
            rfl
          · rw [← hall, hs, List.append_assoc]

#print axioms observeHistory_prefix

/-- Extending a real history observes exactly its new edge. -/
theorem observeHistory_snoc {Error Checkpoint : Type}
    (edge : MachineState → MachineState → Except Error (List Checkpoint))
    (history : List MachineState) (current next : MachineState)
    (events delta : List Checkpoint)
    (last : history.getLast? = some current)
    (observed : observeHistory edge history = .ok events)
    (newEdge : edge current next = .ok delta) :
    observeHistory edge (history ++ [next]) = .ok (events ++ delta) := by
  induction history generalizing events with
  | nil => cases last
  | cons s history ih =>
    cases history with
    | nil =>
      have hs : s = current := Option.some.inj last
      have he : events = [] := (Except.ok.inj observed).symm
      subst s
      subst events
      simp [observeHistory, newEdge]
      change Except.ok (delta ++ []) = Except.ok delta
      rw [List.append_nil]
    | cons t history =>
      have tailLast : (t :: history).getLast? = some current := by simpa using last
      change (do
        let first ← edge s t
        let later ← observeHistory edge (t :: history)
        pure (first ++ later)) = .ok events at observed
      cases hf : edge s t with
      | error e => rw [hf] at observed; cases observed
      | ok first =>
        cases hl : observeHistory edge (t :: history) with
        | error e => rw [hf, hl] at observed; cases observed
        | ok later =>
          rw [hf, hl] at observed
          have he : first ++ later = events := Except.ok.inj observed
          have tail := ih later tailLast hl
          change (do
            let first ← edge s t
            let later ← observeHistory edge ((t :: history) ++ [next])
            pure (first ++ later)) = .ok (events ++ delta)
          rw [hf, tail, ← he, List.append_assoc]
          rfl

#print axioms observeHistory_snoc

/-- Every execution successor appends itself, so the history cursor cannot
    drift away from the physical state, including through service calls. -/
theorem history_last [Labels] (fetch : Int64 → Option Decoded)
    (Q : Executed → Prop) (s : Executed)
    (initial : s.history.getLast? = some s.machine)
    (run : Eventually (historyStep fetch) Q s) :
    Eventually (historyStep fetch)
      (fun t => Q t ∧ t.history.getLast? = some t.machine) s := by
  induction run with
  | done s h => exact .done s ⟨h, initial⟩
  | step s mid hs rest ih =>
    apply step_cps
    apply instruction_mono fetch s.machine _ _ _ hs
    intro t ht
    exact ih ⟨t, s.history ++ [t]⟩ ht (by simp)

#print axioms history_last

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
