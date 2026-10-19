import Leanux.Proofs.Logged.NativeCapture

/-! A transparent dynamic scope for causal roots in the shared journal. Scope
identity is its position in that very journal. An internally stopped body keeps
its entry marker and every earlier effect; it does not invent a successful exit.
Malformed or absent context remains explicit evidence for the caller to reject
in its initialized causal invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

structure Token (Cause : Type) where
  position : Nat
  cause : Cause

inductive Event (Cause : Type) where
  | entered (token : Token Cause)
  | exited (position : Nat)

inductive Malformed where
  | unmatchedExit
  | wrongExit

def advance (state : Except Malformed (List (Token Cause))) (event : Event Cause) :
    Except Malformed (List (Token Cause)) := do
  let stack ← state
  match event with
  | .entered token => pure (token :: stack)
  | .exited position =>
    match stack with
    | [] => .error .unmatchedExit
    | top :: rest => if top.position = position then .ok rest else .error .wrongExit

def stack (history : List (Event Cause)) : Except Malformed (List (Token Cause)) :=
  history.foldl advance (.ok [])

def current (decode : E → Option (Event Cause)) (history : List E) :
    Except Malformed (Option (Token Cause)) := (stack (history.filterMap decode)).map List.head?

def withToken (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → WGPrefix E α) : WGPrefix E α :=
  fun w a => ExceptT.mk fun h =>
    let token : Token Cause := ⟨h.length,cause⟩
    runWGPrefix (do
      emitStatePrefix (record (.entered token))
      let result ← body token
      emitStatePrefix (record (.exited token.position))
      pure result) w a h

def scope (record : Event Cause → E) (cause : Cause) (body : WGPrefix E α) : WGPrefix E α :=
  withToken record cause (fun _ => body)

theorem withToken_run (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → WGPrefix E α) (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (withToken record cause body) w a h =
      match runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
      | (.error stop,history) => (.error stop,history)
      | (.ok result,history) => (.ok result,history ++ [record (.exited h.length)]) := by
  change runStatePrefix (do
    emitStatePrefix (record (.entered ⟨h.length,cause⟩))
    let result ← body ⟨h.length,cause⟩
    emitStatePrefix (record (.exited h.length))
    pure result) w a h = _
  simp only [runStatePrefix_bind,runStatePrefix_emit]
  simp only [runWGPrefix]
  cases runStatePrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    cases result with
    | error stop => rfl
    | ok result => rcases result with ⟨⟨x,v⟩,b⟩; rfl

theorem withToken_erases (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → WGPrefix E α) (native : WG.M α)
    (erases : ∀ token, ErasesStatePrefix (body token) native) :
    ErasesStatePrefix (withToken record cause body) native := by
  intro w a h
  change (runWGPrefix (withToken record cause body) w a h).1 = _
  rw [withToken_run]
  have same := erases ⟨h.length,cause⟩ w a (h ++ [record (.entered ⟨h.length,cause⟩)])
  change (runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)])).1 = _ at same
  cases run : runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    rw [run] at same
    cases result <;> exact same

theorem withToken_projects (record : Event Cause → E) (cause : Cause)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    (body : Token Cause → WGPrefix E α) (target : WGPrefix F α)
    (projects : ∀ token, StateProjectsPrefix ρ id (body token) target) :
    StateProjectsPrefix ρ id (withToken record cause body) target := by
  intro w a h
  have same := projects ⟨h.length,cause⟩ w a (h ++ [record (.entered ⟨h.length,cause⟩)])
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    List.append_nil] at same
  change runStatePrefix target w a (h.filterMap ρ) =
    ((runWGPrefix (withToken record cause body) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),(runWGPrefix (withToken record cause body) w a h).2.filterMap ρ)
  rw [withToken_run]
  cases run : runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    change runStatePrefix target w a (h.filterMap ρ) =
      ((runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)])).1.map
        (fun ((x,v),b) => ((x,v),b)),
        (runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)])).2.filterMap ρ) at same
    rw [run] at same
    cases result with
    | error stop => exact same
    | ok result =>
      simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
        Option.toList_none,List.nil_append,List.append_nil] using same

theorem withToken_entry (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → WGPrefix E α) (appends : ∀ token, StateAppends (body token))
    (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix, (runWGPrefix (withToken record cause body) w a h).2 =
      h ++ record (.entered ⟨h.length,cause⟩) :: suffix := by
  obtain ⟨suffix,hs⟩ := appends ⟨h.length,cause⟩ w a (h ++ [record (.entered ⟨h.length,cause⟩)])
  change (runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)])).2 = _ at hs
  rw [withToken_run]
  cases run : runWGPrefix (body ⟨h.length,cause⟩) w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result history =>
    rw [run] at hs
    change history = _ at hs
    cases result with
    | error stop => exact ⟨suffix,by simpa only [List.append_assoc,List.singleton_append] using hs⟩
    | ok result =>
      exact ⟨suffix ++ [record (.exited h.length)],by
        simp only [hs,List.append_assoc,List.cons_append,List.nil_append]⟩

theorem current_entered (record : Event Cause → E) (decode : E → Option (Event Cause))
    (inverse : ∀ event, decode (record event) = some event) (h : List E)
    (before : List (Token Cause)) (ready : stack (h.filterMap decode) = .ok before)
    (token : Token Cause) :
    current decode (h ++ [record (.entered token)]) = .ok (some token) := by
  simp only [current,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,inverse,
    stack,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (advance (stack (h.filterMap decode)) (.entered token)).map List.head? = _
  rw [ready]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
