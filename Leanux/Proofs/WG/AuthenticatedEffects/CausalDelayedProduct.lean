import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedNative

/-! Product-state transport retains the final journal's live delayed-effect
carrier. Native endpoint frames refer to the actual observed callback and its
own appended history, including old completion/socket receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

theorem product_state {body : WGPrefix Event α} (safe : StateSafe body) :
    ProductSafe (liftWGObserver body) := safe.liftWGObserver

theorem product_wg (native : WG.M α) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (liftPrefix (liftWG native)) := by
  simpa only [liftWGObserver_lift] using product_state safe

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ _ => True.intro) value

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
  PrefixPreserves.forIn xs initial body (fun _ _ _ => True.intro) safe

theorem product_emit (event : Event) : ProductSafe (emitPrefix event) := by
  intro w h hi
  exact ⟨[event],rfl,True.intro,hi.append [event]⟩

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (safe : ∀ token, ProductSafe (body token)) : ProductSafe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)))
    (fun _ => product_bind (safe ⟨h.length,cause⟩) (fun result =>
      product_bind (product_emit (.scope (.exited h.length))) (fun _ => product_pure result))) w h hi

theorem product_capture (body : PrefixM Event α) (safe : ProductSafe body) :
    ProductSafe (captureObserved body) := safe.captureObserved

theorem product_observed (body : PrefixM Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (appends : Appends body)
    (safe : StateSafe (liftWGPrefix native)) : ProductSafe body := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := appends w h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix body w h).1 with
  | error stop => trivial
  | ok result =>
    rcases result with ⟨value,v⟩
    have original := (erases w h).symm.trans run
    obtain ⟨_,_,_,kept⟩ := product_wg native safe w h hi
    have lifted : runPrefix (liftPrefix (liftWG native) : PrefixM Event α) w h =
        (.ok (value,v),h) := by rw [runPrefix_lift,original]
    rw [lifted] at kept
    rw [grown]
    exact kept.append suffix

open Lean Meta Elab Tactic in
elab "causal_delayed_product_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a delayed product contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native product lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

macro "causal_delayed_product_step" : tactic => `(tactic| first
  | (causal_delayed_head Pure.pure; exact product_pure _)
  | (causal_delayed_head Bind.bind; apply product_bind)
  | (causal_delayed_head ite; apply product_ite)
  | (causal_delayed_head ForIn.forIn; apply product_forIn)
  | (causal_delayed_head captureObserved; apply product_capture)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
