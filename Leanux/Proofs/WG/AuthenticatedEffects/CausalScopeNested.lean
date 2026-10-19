import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeProduct
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeBalance

/-! Nested scope contracts distinguish the normal continuation from a stopped
prefix. A normal body restores its incoming stack, while Stop retains a valid
possibly deeper stack. No history frame forbids nested scopes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

variable (decode : E → Option (Event Cause))

def WellFormed (history : List E) : Prop := ∃ frames, stack (history.filterMap decode) = .ok frames

def StateBalanced (body : WGPrefix E α) : Prop :=
  ∀ frames, StatePrefixEnsures (fun h _ _ => stack (h.filterMap decode) = .ok frames)
    (WellFormed decode) body (fun _ h _ _ => stack (h.filterMap decode) = .ok frames)

def ProductBalanced (body : PrefixM E α) : Prop :=
  ∀ frames, PrefixEnsures (fun h (_ : World) => stack (h.filterMap decode) = .ok frames)
    (WellFormed decode) body (fun _ h (_ : World) => stack (h.filterMap decode) = .ok frames)

theorem stack_entered (record : Event Cause → E)
    (inverse : ∀ event, decode (record event) = some event)
    (history : List E) (frames : List (Token Cause)) (token : Token Cause)
    (ready : stack (history.filterMap decode) = .ok frames) :
    stack ((history ++ [record (.entered token)]).filterMap decode) = .ok (token :: frames) := by
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,inverse,stack,
    List.foldl_append,List.foldl_cons,List.foldl_nil]
  change advance (stack (history.filterMap decode)) (.entered token) = _
  rw [ready]
  rfl

theorem stack_exited (record : Event Cause → E)
    (inverse : ∀ event, decode (record event) = some event)
    (history : List E) (frames : List (Token Cause)) (token : Token Cause)
    (ready : stack (history.filterMap decode) = .ok (token :: frames)) :
    stack ((history ++ [record (.exited token.position)]).filterMap decode) = .ok frames := by
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,inverse,stack,
    List.foldl_append,List.foldl_cons,List.foldl_nil]
  change advance (stack (history.filterMap decode)) (.exited token.position) = _
  rw [ready]
  change (if token.position = token.position then Except.ok frames else Except.error Malformed.wrongExit) = _
  simp

theorem state_balanced_lift (body : WG.M α) : StateBalanced decode (liftWGPrefix body) :=
  fun frames => StatePrefixEnsures.lift body (fun _ _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ _ _ ready _ => ready)

theorem state_balanced_pure (value : α) : StateBalanced decode (pure value) :=
  fun frames => StatePrefixEnsures.pure value (fun _ _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ ready => ready)

theorem state_balanced_bind (body : WGPrefix E α) (next : α → WGPrefix E β)
    (first : StateBalanced decode body) (rest : ∀ value, StateBalanced decode (next value)) :
    StateBalanced decode (body >>= next) :=
  fun frames => StatePrefixEnsures.bind (first frames) (fun value => rest value frames)

theorem state_balanced_emit (event : E) (quiet : decode event = none) :
    StateBalanced decode (emitStatePrefix event) := by
  intro frames
  apply StatePrefixEnsures.emit
  · intro h w a ready
    exact ⟨frames,by simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      quiet,Option.toList_none,List.nil_append,List.append_nil] using ready⟩
  · intro h w a ready
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      quiet,Option.toList_none,List.nil_append,List.append_nil] using ready

theorem state_balanced_frame (body : WGPrefix E α) (appends : StateAppends body)
    (frame : StateHistoryFrame decode body) : StateBalanced decode body := by
  intro frames w a h ready
  obtain ⟨suffix,grown⟩ := appends w a h
  have kept : stack ((runPrefix (body.run w) a h).2.filterMap decode) = .ok frames := by
    rw [frame w a h]
    exact ready
  refine ⟨suffix,grown,⟨frames,kept⟩,?_⟩
  cases (runPrefix (body.run w) a h).1 with
  | error _ => trivial
  | ok result => rcases result with ⟨⟨value,v⟩,b⟩; exact kept

/-- Normal completion pops the precise scope that this call entered, even
when the body ran and closed other scopes. An internal Stop keeps those entries. -/
theorem withToken_balanced (record : Event Cause → E)
    (inverse : ∀ event, decode (record event) = some event)
    (cause : Cause) (body : Token Cause → WGPrefix E α)
    (balanced : ∀ token, StateBalanced decode (body token)) :
    StateBalanced decode (withToken record cause body) := by
  intro frames w a h ready
  let token : Token Cause := ⟨h.length,cause⟩
  let entered := h ++ [record (.entered token)]
  have pushed : stack (entered.filterMap decode) = .ok (token :: frames) :=
    stack_entered decode record inverse h frames token ready
  obtain ⟨suffix,grown,valid,normal⟩ := balanced token (token :: frames) w a entered pushed
  change (runWGPrefix (body token) w a entered).2 = entered ++ suffix at grown
  change WellFormed decode (runWGPrefix (body token) w a entered).2 at valid
  have equation := withToken_run record cause body w a h
  change runPrefix (StateT.run (withToken record cause body) w) a h = _ at equation
  cases run : runWGPrefix (body token) w a entered with
  | mk result history =>
    rw [run] at grown valid
    change history = entered ++ suffix at grown
    have normalRun := run
    change runPrefix ((body token).run w) a entered = (result,history) at normalRun
    rw [normalRun] at normal
    dsimp only [token,entered] at run
    rw [run] at equation
    rw [equation]
    cases result with
    | error stop =>
      exact ⟨record (.entered token) :: suffix,
        by simpa only [entered,List.append_assoc,List.singleton_append] using grown,valid,True.intro⟩
    | ok result =>
      rcases result with ⟨⟨value,v⟩,b⟩
      have popped := stack_exited decode record inverse history frames token normal
      exact ⟨record (.entered token) :: (suffix ++ [record (.exited h.length)]),
        by simp only [grown,entered,List.append_assoc,List.cons_append,List.nil_append],⟨frames,popped⟩,popped⟩

theorem scope_balanced (record : Event Cause → E)
    (inverse : ∀ event, decode (record event) = some event) (cause : Cause)
    (body : WGPrefix E α) (balanced : StateBalanced decode body) :
    StateBalanced decode (scope record cause body) :=
  withToken_balanced decode record inverse cause (fun _ => body) (fun _ => balanced)


theorem product_balanced_lift (body : Leanux.M α) : ProductBalanced decode (liftPrefix body) :=
  fun frames => PrefixEnsures.lift body (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready _ => ready)

theorem product_balanced_pure (value : α) : ProductBalanced decode (pure value) :=
  fun frames => PrefixEnsures.pure (fun _ _ ready => ⟨frames,ready⟩) (fun _ _ ready => ready)

theorem product_balanced_bind (body : PrefixM E α) (next : α → PrefixM E β)
    (first : ProductBalanced decode body) (rest : ∀ value, ProductBalanced decode (next value)) :
    ProductBalanced decode (body >>= next) :=
  fun frames => PrefixEnsures.bind (first frames) (fun value => rest value frames)

theorem product_balanced_state (body : WGPrefix E α) (balanced : StateBalanced decode body) :
    ProductBalanced decode (liftWGObserver body) := fun frames => (balanced frames).liftWGObserver

theorem product_balanced_frame (body : PrefixM E α) (appends : Appends body)
    (frame : HistoryFrame decode body) : ProductBalanced decode body := by
  intro frames w h ready
  obtain ⟨suffix,grown⟩ := appends w h
  have kept : stack ((runPrefix body w h).2.filterMap decode) = .ok frames := by
    rw [frame w h]
    exact ready
  refine ⟨suffix,grown,⟨frames,kept⟩,?_⟩
  cases (runPrefix body w h).1 with
  | error _ => trivial
  | ok result => rcases result with ⟨value,v⟩; exact kept

theorem prefix_balanced (record : Event Cause → E)
    (inverse : ∀ event, decode (record event) = some event)
    (cause : Cause) (body : Token Cause → PrefixM E α)
    (balanced : ∀ token, ProductBalanced decode (body token)) :
    ProductBalanced decode (prefixScope record cause body) := by
  intro frames w h ready
  let token : Token Cause := ⟨h.length,cause⟩
  let entered := h ++ [record (.entered token)]
  have pushed : stack (entered.filterMap decode) = .ok (token :: frames) :=
    stack_entered decode record inverse h frames token ready
  obtain ⟨suffix,grown,valid,normal⟩ := balanced token (token :: frames) w entered pushed
  have equation := prefix_run record cause body w h
  cases run : runPrefix (body token) w entered with
  | mk result history =>
    rw [run] at grown valid normal
    change history = entered ++ suffix at grown
    dsimp only [token,entered] at run
    rw [run] at equation
    rw [equation]
    cases result with
    | error stop =>
      exact ⟨record (.entered token) :: suffix,
        by simpa only [entered,List.append_assoc,List.singleton_append] using grown,valid,True.intro⟩
    | ok result =>
      rcases result with ⟨value,v⟩
      have popped := stack_exited decode record inverse history frames token normal
      exact ⟨record (.entered token) :: (suffix ++ [record (.exited h.length)]),
        by simp only [grown,entered,List.append_assoc,List.cons_append,List.nil_append],⟨frames,popped⟩,popped⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
