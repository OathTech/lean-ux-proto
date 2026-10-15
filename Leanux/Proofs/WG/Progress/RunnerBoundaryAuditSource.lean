import Leanux.Proofs.WG.Progress.RunnerBoundarySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Lean Leanux Leanux.Runner Campaign2

def runnerEntry (trace : Trace) (state : RunnerAccumulator) : World :=
  { state.1 with hidden := trace.hidden.map (·[state.2.1.size]!), netRxRaised := false }

theorem runnerOperation_facts (trace : Trace) (op : Operation) (state : RunnerAccumulator)
    (ret : Int) (after : World) (run : runnerOperation trace op state = .ok (ret, after)) :
    (∃ middle, (syscall (toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run
        (runnerEntry trace state) = .ok (ret, middle) ∧
      skipAmbient.run middle = .ok ((), after)) ∧
    RunnerBoundaryClean ⟨state.2.1.size, ret, snapshot after⟩ := by
  unfold runnerOperation at run
  change ((Except.mapError (fun e => (state.2.1.size, e))
    ((syscall (toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run
      (runnerEntry trace state))) >>= _) = _ at run
  cases hs : (syscall (toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run
      (runnerEntry trace state) with
  | error error => simp [hs, Except.mapError, bind, Except.bind] at run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    simp only [hs, Except.mapError, Bind.bind, Except.bind] at run
    cases ha : skipAmbient.run middle with
    | error error => simp [ha, Except.mapError, bind, Except.bind] at run
    | ok pair =>
      obtain ⟨u, final⟩ := pair
      cases u
      simp only [ha, Except.mapError, Bind.bind, Except.bind] at run
      cases hh : final.hidden with
      | none =>
        cases hsusp : final.suspended <;> cases hn : final.netRxRaised
        all_goals simp [hh, hsusp, hn, pure, Except.pure, bind, Except.bind] at run
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals exact ⟨⟨middle, rfl, ha⟩, by simp [RunnerBoundaryClean, snapshot, hh, hsusp, hn]⟩
      | some records =>
        cases records with
        | cons record rest => simp [hh, pure, Except.pure, bind, Except.bind] at run
        | nil =>
          cases hsusp : final.suspended <;> cases hn : final.netRxRaised
          all_goals simp [hh, hsusp, hn, pure, Except.pure, bind, Except.bind] at run
          all_goals obtain ⟨rfl, rfl⟩ := run
          all_goals exact ⟨⟨middle, rfl, ha⟩, by simp [RunnerBoundaryClean, snapshot, hh, hsusp, hn]⟩

theorem runnerPresent_facts (op : Operation) (state : RunnerAccumulator) (ret : Int)
    (after : World) (step : ForInStep RunnerAccumulator)
    (run : runnerPresent op state ret after = .ok step) :
    ∃ next, step = .yield next ∧ next.1 = after ∧ next.2.1 = state.2.1.push ret := by
  unfold runnerPresent at run
  simp only [Bind.bind, Except.bind] at run
  split at run
  · cases run
  · split at run
    · cases run
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at run
      subst step
      exact ⟨_, rfl, rfl, rfl⟩

theorem runnerStep_facts (trace : Trace) (op : Operation) (state : RunnerAccumulator)
    (step : ForInStep RunnerAccumulator) (run : runnerStep trace op state = .ok step) :
    ∃ next ret, step = .yield next ∧ next.2.1 = state.2.1.push ret ∧
      runnerOperation trace op state = .ok (ret, next.1) ∧
      RunnerBoundaryClean ⟨state.2.1.size, ret, snapshot next.1⟩ := by
  rw [runnerStep_operation_source] at run
  cases hr : runnerOperation trace op state with
  | error error => simp [hr, bind, Except.bind] at run
  | ok pair =>
    obtain ⟨ret, after⟩ := pair
    simp only [hr, Bind.bind, Except.bind] at run
    obtain ⟨next, rfl, rfl, results⟩ := runnerPresent_facts op state ret after step run
    exact ⟨next, ret, rfl, results, rfl, (runnerOperation_facts trace op state ret next.1 hr).2⟩

/-- On successful loop return, every operation contributes exactly one boundary.
The continuation uses the actual presentation state, including descriptor
bookkeeping. A later error discards the observation list. -/
def runnerAuditLoop (trace : Trace) : List Operation → RunnerAccumulator →
    Except (Nat × Stop) (RunnerAccumulator × List RunnerBoundary)
  | [], state => .ok (state, [])
  | op :: ops, state => do
    let (ret, after) ← runnerOperation trace op state
    let step ← runnerPresent op state ret after
    let cut : RunnerBoundary := ⟨state.2.1.size, ret, snapshot after⟩
    match step with
    | .done next => return (next, [cut])
    | .yield next =>
      let (final, cuts) ← runnerAuditLoop trace ops next
      return (final, cut :: cuts)

theorem runnerAuditLoop_cons_success (trace : Trace) (op : Operation) (ops : List Operation)
    (state final : RunnerAccumulator) (cuts : List RunnerBoundary)
    (run : runnerAuditLoop trace (op :: ops) state = .ok (final, cuts)) :
    ∃ ret after next rest,
      runnerOperation trace op state = .ok (ret, after) ∧
      next.1 = after ∧ next.2.1 = state.2.1.push ret ∧
      runnerAuditLoop trace ops next = .ok (final, rest) ∧
      cuts = ⟨state.2.1.size, ret, snapshot after⟩ :: rest := by
  simp only [runnerAuditLoop] at run
  cases ho : runnerOperation trace op state with
  | error error => simp [ho, Bind.bind, Except.bind] at run
  | ok pair =>
    obtain ⟨ret, after⟩ := pair
    simp only [ho, Bind.bind, Except.bind] at run
    cases hp : runnerPresent op state ret after with
    | error error => simp [hp, Bind.bind, Except.bind] at run
    | ok step =>
      obtain ⟨next, rfl, hw, hr⟩ := runnerPresent_facts op state ret after step hp
      simp only [hp, Bind.bind, Except.bind] at run
      cases hl : runnerAuditLoop trace ops next with
      | error error => simp [hl, Bind.bind, Except.bind] at run
      | ok pair =>
        obtain ⟨last, rest⟩ := pair
        simp only [hl, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨ret, after, next, rest, rfl, hw, hr, hl, rfl⟩

theorem runnerAuditLoop_erases (trace : Trace) (ops : List Operation)
    (state : RunnerAccumulator) :
    (runnerAuditLoop trace ops state).map Prod.fst = forIn ops state (runnerStep trace) := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    simp only [runnerAuditLoop, List.forIn_cons, runnerStep_operation_source]
    cases ho : runnerOperation trace op state with
    | error error => rfl
    | ok pair =>
      obtain ⟨ret, after⟩ := pair
      simp only [Bind.bind, Except.bind]
      cases hp : runnerPresent op state ret after with
      | error error => rfl
      | ok step =>
        cases step with
        | done next => rfl
        | yield next =>
          specialize ih next
          cases hl : runnerAuditLoop trace ops next <;>
            simp_all [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem runnerAuditLoop_facts (trace : Trace) (ops : List Operation)
    (state final : RunnerAccumulator) (cuts : List RunnerBoundary)
    (run : runnerAuditLoop trace ops state = .ok (final, cuts)) :
    cuts.map RunnerBoundary.index = List.range' state.2.1.size ops.length ∧
    (∀ cut ∈ cuts, RunnerBoundaryClean cut) ∧
    final.2.1.size = state.2.1.size + ops.length := by
  induction ops generalizing state final cuts with
  | nil =>
    simp only [runnerAuditLoop, Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    simp
  | cons op ops ih =>
    simp only [runnerAuditLoop] at run
    cases ho : runnerOperation trace op state with
    | error error => simp [ho, Bind.bind, Except.bind] at run
    | ok pair =>
      obtain ⟨ret, after⟩ := pair
      simp only [ho, Bind.bind, Except.bind] at run
      cases hp : runnerPresent op state ret after with
      | error error => simp [hp, Bind.bind, Except.bind] at run
      | ok step =>
        obtain ⟨next, rfl, hw, hr⟩ := runnerPresent_facts op state ret after step hp
        simp only [hp, Bind.bind, Except.bind] at run
        cases hl : runnerAuditLoop trace ops next with
        | error error => simp [hl, Bind.bind, Except.bind] at run
        | ok pair =>
          obtain ⟨last, rest⟩ := pair
          simp only [hl, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          obtain ⟨indices, clean, size⟩ := ih next last rest hl
          have stepClean := (runnerOperation_facts trace op state ret after ho).2
          have nextSize : next.2.1.size = state.2.1.size + 1 := by simp [hr]
          refine ⟨?_, ?_, ?_⟩
          · simp [indices, List.range'_succ, nextSize]
          · intro cut member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact stepClean
            · exact clean cut member
          · simp only [List.length_cons]
            omega

def executeTraceWithBoundaries (trace : Trace) (placeholders floodExact : Bool := false) :
    Except (Nat × Stop) RunnerBoundaryAudit := do
  let initial ← runnerInitial trace placeholders floodExact
  let (final, cuts) ← runnerAuditLoop trace trace.ops.toList
    (initial, #[], #[], #[], #[], #[])
  let output ← runnerFinish trace final
  return ⟨output, cuts⟩

theorem executeTraceWithBoundaries_erases (trace : Trace) (placeholders floodExact : Bool) :
    (executeTraceWithBoundaries trace placeholders floodExact).map RunnerBoundaryAudit.output =
      executeTrace trace placeholders floodExact := by
  rw [← executeTrace_boundary_source]
  unfold executeTraceWithBoundaries runnerBoundarySource
  cases hi : runnerInitial trace placeholders floodExact with
  | error error => rfl
  | ok initial =>
    simp only [Bind.bind, Except.bind]
    rw [← Array.forIn_toList, ← runnerAuditLoop_erases]
    cases hl : runnerAuditLoop trace trace.ops.toList (initial, #[], #[], #[], #[], #[]) with
    | error error => rfl
    | ok pair =>
      obtain ⟨final, cuts⟩ := pair
      simp only [Except.map, Bind.bind, Except.bind]
      cases runnerFinish trace final <;> rfl

theorem executeTraceWithBoundaries_facts (trace : Trace) (placeholders floodExact : Bool)
    (audit : RunnerBoundaryAudit)
    (run : executeTraceWithBoundaries trace placeholders floodExact = .ok audit) :
    audit.boundaries.map RunnerBoundary.index = List.range trace.ops.size ∧
    audit.boundaries.length = trace.ops.size ∧
    ∀ cut ∈ audit.boundaries, RunnerBoundaryClean cut := by
  unfold executeTraceWithBoundaries at run
  cases hi : runnerInitial trace placeholders floodExact with
  | error error => simp [hi, Bind.bind, Except.bind] at run
  | ok initial =>
    simp only [hi, Bind.bind, Except.bind] at run
    cases hl : runnerAuditLoop trace trace.ops.toList (initial, #[], #[], #[], #[], #[]) with
    | error error => simp [hl, Bind.bind, Except.bind] at run
    | ok pair =>
      obtain ⟨final, cuts⟩ := pair
      simp only [hl, Bind.bind, Except.bind] at run
      cases hf : runnerFinish trace final with
      | error error => simp [hf, Bind.bind, Except.bind] at run
      | ok output =>
        simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at run
        subst audit
        obtain ⟨indices, clean, _⟩ := runnerAuditLoop_facts trace trace.ops.toList
          (initial, #[], #[], #[], #[], #[]) final cuts hl
        have eqIndices : cuts.map RunnerBoundary.index = List.range trace.ops.size := by
          simpa [List.range_eq_range'] using indices
        exact ⟨eqIndices, by simpa using congrArg List.length eqIndices, clean⟩

end Leanux.Proofs.WG.Progress
