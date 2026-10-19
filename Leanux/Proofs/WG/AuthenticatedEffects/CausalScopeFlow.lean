import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeNested
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Normal-return scope balance composes through the actual native control
operators. These contracts permit nested scopes and preserve open Stop prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev StateSafe (body : WGPrefix Event α) := CausalScope.StateBalanced scope? body
abbrev ProductSafe (body : PrefixM Event α) := CausalScope.ProductBalanced scope? body

theorem state_lift (body : WG.M α) : StateSafe (liftWGPrefix body) := CausalScope.state_balanced_lift scope? body
theorem state_pure (value : α) : StateSafe (pure value) := CausalScope.state_balanced_pure scope? value
theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (first : StateSafe body) (rest : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  CausalScope.state_balanced_bind scope? body next first rest

theorem state_ite (p : Prop) [Decidable p] {a b : WGPrefix Event α}
    (ha : p → StateSafe a) (hb : ¬p → StateSafe b) : StateSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem state_forIn (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value state, StateSafe (body value state)) : StateSafe (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact state_pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply state_bind (safe x initial)
    intro step
    cases step with
    | done state => exact state_pure state
    | yield state => exact ih state

theorem state_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value state, StateSafe (body value state)) : StateSafe (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ initial body safe

theorem state_emit (event : Event) (quiet : scope? event = none) : StateSafe (emitStatePrefix event) :=
  CausalScope.state_balanced_emit scope? event quiet

theorem state_capture (body : WGPrefix Event α) (safe : StateSafe body) : StateSafe (captureWGObserved body) := by
  intro frames
  exact StatePrefixPreserves.captureWGObserved (safe frames)

theorem state_receipt (body : WGPrefix Event α) (safe : StateSafe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, scope? (record r) = none) :
    StateSafe (receiptWGObserved body record) :=
  state_bind (state_capture body safe) (fun r =>
    state_bind (state_emit (record r) (quiet r)) (fun _ => state_pure r.value))

theorem state_focus (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, scope? (encode event) = none) (body : WGPrefix F α) :
    StateSafe (focusStatePrefix encode decode body) :=
  CausalScope.state_balanced_frame scope? _ (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other encode decode scope? quiet (body.run w))

theorem state_scope (cause : Cause) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_balanced scope? Event.scope (fun _ => rfl) cause body safe

theorem state_current (body : Context → WGPrefix Event α) (safe : ∀ context, StateSafe (body context)) :
    StateSafe (CausalEffects.atCurrent scope? body) := by
  intro frames w a history ready
  exact safe (CausalScope.current scope? history) frames w a history ready

theorem product_lift (body : Leanux.M α) : ProductSafe (liftPrefix body) := CausalScope.product_balanced_lift scope? body
theorem product_pure (value : α) : ProductSafe (pure value) := CausalScope.product_balanced_pure scope? value
theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (first : ProductSafe body) (rest : ∀ value, ProductSafe (next value)) : ProductSafe (body >>= next) :=
  CausalScope.product_balanced_bind scope? body next first rest

theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Event α}
    (ha : p → ProductSafe a) (hb : ¬p → ProductSafe b) : ProductSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem product_forIn (xs : List α) (initial : β) (body : α → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact product_pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply product_bind (safe x initial)
    intro step
    cases step with
    | done state => exact product_pure state
    | yield state => exact ih state

theorem product_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ initial body safe

theorem product_state (body : WGPrefix Event α) (safe : StateSafe body) : ProductSafe (liftWGObserver body) :=
  CausalScope.product_balanced_state scope? body safe

theorem product_capture (body : PrefixM Event α) (safe : ProductSafe body) : ProductSafe (captureObserved body) := by
  intro frames
  exact PrefixPreserves.captureObserved (safe frames)

theorem product_focus (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, scope? (encode event) = none) (body : PrefixM F α) :
    ProductSafe (focusPrefix encode decode body) :=
  CausalScope.product_balanced_frame scope? _ (Appends.focus _ _ _)
    (focusPrefix_other encode decode scope? quiet body)

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (safe : ∀ token, ProductSafe (body token)) : ProductSafe (CausalScope.prefixScope Event.scope cause body) :=
  CausalScope.prefix_balanced scope? Event.scope (fun _ => rfl) cause body safe

open Lean Meta Elab Tactic in
elab "scope_balance_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not a scope-balance contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData.headBeta
  let action ← if action.isAppOf ``liftWGObserver then do
    let inner := action.getAppArgs
    unless inner.size > 0 do throwError "missing lifted action"
    pure inner.back!.consumeMData
    else pure action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "scope_balance_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not a scope-balance contract"
  let rec head : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else head n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else head n next
        | _ => e
  let .app f action := target | throwError "missing action"
  let next := if action.isAppOf ``liftWGObserver then
      match action with
      | .app outer inner => mkApp outer (head 64 inner)
      | _ => action
    else head 64 action
  if Expr.equal action next then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkApp f next)]

macro "scope_state_step" : tactic => `(tactic| first
  | (scope_balance_head liftWGPrefix; exact state_lift _)
  | (scope_balance_head Pure.pure; exact state_pure _)
  | (scope_balance_head Bind.bind; apply state_bind)
  | (scope_balance_head ite; apply state_ite)
  | (scope_balance_head ForIn.forIn; first | apply state_forIn | apply state_range)
  | maintenance_intro
  | scope_balance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

macro "scope_product_step" : tactic => `(tactic| first
  | (scope_balance_head liftPrefix; exact product_lift _)
  | (scope_balance_head liftWGPrefix; exact product_state _ (state_lift _))
  | (scope_balance_head Pure.pure; exact product_pure _)
  | (scope_balance_head Bind.bind; apply product_bind)
  | (scope_balance_head ite; apply product_ite)
  | (scope_balance_head ForIn.forIn; first | apply product_forIn | apply product_range)
  | maintenance_intro
  | scope_balance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
