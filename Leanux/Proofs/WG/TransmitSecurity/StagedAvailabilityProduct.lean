import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityAdapters

/-! Product-state adapters for exact positional staged origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

abbrev ProductSafe (action : PrefixM Event α) := PrefixPreserves (fun h w => Carrier h w.wg) Safe action

theorem product_state {body : WGPrefix Event α} (safe : StateSafe body) :
    ProductSafe (liftWGObserver body) := safe.liftWGObserver

theorem product_wg (native : WG.M α) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (liftPrefix (liftWG native)) := by
  simpa only [liftWGObserver_lift] using product_state safe

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ before => before.2) value

theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (safe : ProductSafe body) (tail : ∀ value, ProductSafe (next value)) :
    ProductSafe (body >>= next) := PrefixPreserves.bind safe tail

theorem product_ite (p : Prop) [Decidable p] {left right : PrefixM Event α}
    (hl : p → ProductSafe left) (hr : ¬p → ProductSafe right) :
    ProductSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem product_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn xs initial body) :=
  PrefixPreserves.forIn xs initial body (fun _ _ before => before.2) safe

theorem product_emit (event : Event) (quiet : allocation? event = none) : ProductSafe (emitPrefix event) := by
  intro w h before
  have safe := before.2.emit (quiet_event quiet)
  exact ⟨[event],rfl,safe,before.1.append (quiet_singleton quiet),safe⟩

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (safe : ∀ token, ProductSafe (body token)) : ProductSafe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)) rfl)
    (fun _ => product_bind (safe ⟨h.length,cause⟩) (fun result =>
      product_bind (product_emit (.scope (.exited h.length)) rfl) (fun _ => product_pure result))) w h hi

theorem product_capture (body : PrefixM Event α) (safe : ProductSafe body) :
    ProductSafe (captureObserved body) := safe.captureObserved

open Lean Meta Elab Tactic in
elab "available_origin_product_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a available-birth product contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native product lift"
  let some native := action.getAppArgs.back? | throwError "missing native action"
  let native := native.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

open Lean Meta Elab Tactic in
elab "available_origin_product_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a available-birth product contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  let action ← if action.isAppOf ``liftWGObserver then
      match action.getAppArgs.back? with
      | some body => pure body.consumeMData
      | none => throwError "missing WireGuard observer body"
    else pure action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

macro "available_origin_product_step" : tactic => `(tactic| first
  | (available_origin_product_head Pure.pure; exact product_pure _)
  | (available_origin_product_head Bind.bind; apply product_bind)
  | (available_origin_product_head ite; apply product_ite)
  | (available_origin_product_head ForIn.forIn; apply product_forIn)
  | (available_origin_product_head captureObserved; apply product_capture)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
