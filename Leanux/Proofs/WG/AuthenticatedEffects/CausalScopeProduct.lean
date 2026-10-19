import Leanux.Proofs.WG.AuthenticatedEffects.CausalScope

/-! The same transparent root scope at the shared product-driver boundary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

def enterPrefix (record : Event Cause → E) (cause : Cause) : PrefixT E State Nat :=
  fun w => ExceptT.mk fun h =>
    (.ok (h.length,w),h ++ [record (.entered ⟨h.length,cause⟩)])

def leavePrefix (record : Event Cause → E) (position : Nat) : PrefixT E State Unit :=
  emitPrefix (record (.exited position))

theorem enter_projects (record : Event Cause → E) (cause : Cause) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) :
    ProjectsPrefix (State := State) ρ (fun _ => 0) (enterPrefix record cause) (pure 0) := by
  intro w h
  change (Except.ok (ε := Stop) (0,w),h.filterMap ρ) =
    (Except.ok (ε := Stop) (0,w),(h ++ [record (.entered ⟨h.length,cause⟩)]).filterMap ρ)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,List.append_nil]

theorem leave_projects (record : Event Cause → E) (position : Nat) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) :
    ProjectsPrefix (State := State) ρ id (leavePrefix record position) (pure ()) := by
  simpa only [leavePrefix,quiet,Option.elim_none] using
    (projectsPrefix_emit (State := State) ρ (record (.exited position)))

def prefixScope (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → PrefixT E State α) : PrefixT E State α :=
  fun w => ExceptT.mk fun h =>
    let token : Token Cause := ⟨h.length,cause⟩
    runPrefix (do
      emitPrefix (record (.entered token))
      let result ← body token
      emitPrefix (record (.exited token.position))
      pure result) w h

theorem prefix_run (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → PrefixT E State α) (w : State) (h : List E) :
    runPrefix (prefixScope record cause body) w h =
      match runPrefix (body ⟨h.length,cause⟩) w (h ++ [record (.entered ⟨h.length,cause⟩)]) with
      | (.error stop,history) => (.error stop,history)
      | (.ok result,history) => (.ok result,history ++ [record (.exited h.length)]) := by
  change runPrefix (do
    emitPrefix (record (.entered ⟨h.length,cause⟩))
    let result ← body ⟨h.length,cause⟩
    emitPrefix (record (.exited h.length))
    pure result) w h = _
  simp only [runPrefix_bind,runPrefix_emit]
  cases runPrefix (body ⟨h.length,cause⟩) w (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    cases result with
    | error stop => rfl
    | ok result => rcases result with ⟨x,v⟩; rfl

theorem prefix_erases (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → PrefixT E State α) (native : StateT State (Except Stop) α)
    (erases : ∀ token, ErasesPrefix (body token) native) :
    ErasesPrefix (prefixScope record cause body) native := by
  intro w h
  rw [prefix_run]
  have same := erases ⟨h.length,cause⟩ w (h ++ [record (.entered ⟨h.length,cause⟩)])
  cases run : runPrefix (body ⟨h.length,cause⟩) w (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    rw [run] at same
    cases result <;> exact same

theorem prefix_projects (record : Event Cause → E) (cause : Cause)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    (body : Token Cause → PrefixT E State α) (target : PrefixT F State α)
    (projects : ∀ token, ProjectsPrefix ρ id (body token) target) :
    ProjectsPrefix ρ id (prefixScope record cause body) target := by
  intro w h
  have same := projects ⟨h.length,cause⟩ w (h ++ [record (.entered ⟨h.length,cause⟩)])
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    List.append_nil] at same
  rw [prefix_run]
  cases run : runPrefix (body ⟨h.length,cause⟩) w (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    rw [run] at same
    cases result with
    | error stop => exact same
    | ok result =>
      simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
        Option.toList_none,List.nil_append,List.append_nil] using same

theorem prefix_entry (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → PrefixT E State α) (appends : ∀ token, Appends (body token))
    (w : State) (h : List E) :
    ∃ suffix, (runPrefix (prefixScope record cause body) w h).2 =
      h ++ record (.entered ⟨h.length,cause⟩) :: suffix := by
  obtain ⟨suffix,hs⟩ := appends ⟨h.length,cause⟩ w (h ++ [record (.entered ⟨h.length,cause⟩)])
  rw [prefix_run]
  cases run : runPrefix (body ⟨h.length,cause⟩) w (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    rw [run] at hs
    change history = _ at hs
    cases result with
    | error stop => exact ⟨suffix,by simpa only [List.append_assoc,List.singleton_append] using hs⟩
    | ok result =>
      exact ⟨suffix ++ [record (.exited h.length)],by
        simp only [hs,List.append_assoc,List.cons_append,List.nil_append]⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
