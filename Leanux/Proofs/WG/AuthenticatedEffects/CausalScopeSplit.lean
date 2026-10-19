import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFlow

/-! Matched split callbacks carry the precise returned token into the native
continuation. Exit is proved only for that current top token, not an arbitrary ID. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Flow (before after : List (CausalScope.Token Cause)) (body : PrefixM Event α) :=
  PrefixEnsures (fun h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok before)
    (CausalScope.WellFormed scope?) body
    (fun _ h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok after)

theorem universal (body : PrefixM Event α) (safe : ∀ frames, Flow frames frames body) : ProductSafe body := safe

theorem flow_pure (frames : List (CausalScope.Token Cause)) (value : α) : Flow frames frames (pure value) :=
  product_pure value frames

theorem flow_bind (body : PrefixM Event α) (next : α → PrefixM Event β)
    (before after : List (CausalScope.Token Cause)) (safe : ProductSafe body)
    (tail : ∀ value, Flow before after (next value)) : Flow before after (body >>= next) :=
  PrefixEnsures.bind (safe before) tail

theorem flow_ite (before after : List (CausalScope.Token Cause)) (p : Prop) [Decidable p]
    (a b : PrefixM Event α) (ha : p → Flow before after a) (hb : ¬p → Flow before after b) :
    Flow before after (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem enter_checked (cause : Cause) (frames : List (CausalScope.Token Cause)) :
    PrefixEnsures (fun h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok frames)
      (CausalScope.WellFormed scope?) (CausalScope.enterPrefix Event.scope cause)
      (fun index h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok (⟨index,cause⟩ :: frames)) := by
  intro w h ready
  have pushed := CausalScope.stack_entered scope? Event.scope (fun _ => rfl) h frames ⟨h.length,cause⟩ ready
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,⟨_,pushed⟩,pushed⟩

theorem enter_bind (cause : Cause) (next : Nat → PrefixM Event α)
    (before after : List (CausalScope.Token Cause))
    (tail : ∀ index, Flow (⟨index,cause⟩ :: before) after (next index)) :
    Flow before after (CausalScope.enterPrefix Event.scope cause >>= next) :=
  PrefixEnsures.bind (enter_checked cause before) tail

theorem leave_checked (index : Nat) (cause : Cause) (frames : List (CausalScope.Token Cause)) :
    Flow (⟨index,cause⟩ :: frames) frames (CausalScope.leavePrefix Event.scope index) := by
  intro w h ready
  have popped := CausalScope.stack_exited scope? Event.scope (fun _ => rfl) h frames ⟨index,cause⟩ ready
  exact ⟨[.scope (.exited index)],rfl,⟨_,popped⟩,popped⟩

theorem leave_bind (index : Nat) (cause : Cause) (next : Unit → PrefixM Event α)
    (before after : List (CausalScope.Token Cause))
    (tail : ∀ value, Flow before after (next value)) :
    Flow (⟨index,cause⟩ :: before) after (CausalScope.leavePrefix Event.scope index >>= next) :=
  PrefixEnsures.bind (leave_checked index cause before) tail

open Lean Meta Elab Tactic in
elab "scope_first_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe || target.isAppOf ``Flow do throwError "not a scope flow"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let parts := action.getAppArgs
  unless parts.size ≥ 2 do throwError "missing first action"
  let first := parts[parts.size-2]!.consumeMData.headBeta
  let .const actual _ := first.getAppFn | throwError "not a constant first action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different first action"

open Lean Meta Elab Tactic in
elab "scope_flow_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Flow do throwError "not a split scope flow"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different action"

macro "scope_flow_step" : tactic => `(tactic| first
  | (scope_first_head CausalSources.candidateEnter; apply enter_bind)
  | (scope_first_head CausalScope.leavePrefix; apply leave_bind)
  | (scope_flow_head Pure.pure; exact flow_pure _ _)
  | (scope_flow_head Bind.bind; apply flow_bind)
  | (scope_flow_head ite; apply flow_ite)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
