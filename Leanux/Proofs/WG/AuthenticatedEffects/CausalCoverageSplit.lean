import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageQuiet

/-! Exact split token continuations establish coverage only inside the scope
they actually entered. Arbitrary leave callbacks have no preservation contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Flow (before after : List (CausalScope.Token Cause)) (body : PrefixM Event α) :=
  PrefixEnsures (fun h (_ : World) => Inv before h) Safe body (fun _ h (_ : World) => Inv after h)

theorem flow_pure (frames : List (CausalScope.Token Cause)) (value : α) : Flow frames frames (pure value) := product_pure value

theorem flow_bind (body : PrefixM Event α) (next : α → PrefixM Event β)
    (before after : List (CausalScope.Token Cause)) (safe : ProductAt before body)
    (tail : ∀ value, Flow before after (next value)) : Flow before after (body >>= next) :=
  PrefixEnsures.bind safe tail

theorem flow_ite (before after : List (CausalScope.Token Cause)) (p : Prop) [Decidable p]
    (a b : PrefixM Event α) (ha : p → Flow before after a) (hb : ¬p → Flow before after b) :
    Flow before after (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem enter_checked (cause : Cause) (other : Other cause) (frames : List (CausalScope.Token Cause)) :
    PrefixEnsures (fun h (_ : World) => Inv frames h) Safe (CausalScope.enterPrefix Event.scope cause)
      (fun index h (_ : World) => Inv (⟨index,cause⟩ :: frames) h) := by
  intro w h ready
  have pushed := ready.enter ⟨h.length,cause⟩ other
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,pushed.1,pushed⟩

theorem enter_bind (cause : Cause) (other : Other cause) (next : Nat → PrefixM Event α)
    (before after : List (CausalScope.Token Cause))
    (tail : ∀ index, Flow (⟨index,cause⟩ :: before) after (next index)) :
    Flow before after (CausalScope.enterPrefix Event.scope cause >>= next) :=
  PrefixEnsures.bind (enter_checked cause other before) tail

theorem leave_checked (index : Nat) (cause : Cause) (frames : List (CausalScope.Token Cause)) :
    Flow (⟨index,cause⟩ :: frames) frames (CausalScope.leavePrefix Event.scope index) := by
  intro w h ready
  have popped := ready.leave
  exact ⟨[.scope (.exited index)],rfl,popped.1,popped⟩

theorem leave_bind (index : Nat) (cause : Cause) (next : Unit → PrefixM Event α)
    (before after : List (CausalScope.Token Cause))
    (tail : ∀ value, Flow before after (next value)) :
    Flow (⟨index,cause⟩ :: before) after (CausalScope.leavePrefix Event.scope index >>= next) :=
  PrefixEnsures.bind (leave_checked index cause before) tail

open Lean Meta Elab Tactic in
elab "coverage_first_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductAt || target.isAppOf ``Flow do throwError "not a coverage flow"
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
elab "coverage_flow_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Flow do throwError "not a split coverage flow"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different action"

macro "coverage_flow_step" : tactic => `(tactic| first
  | (coverage_first_head CausalSources.candidateEnter; apply enter_bind)
  | (coverage_first_head CausalScope.leavePrefix; apply leave_bind)
  | (coverage_flow_head Pure.pure; exact flow_pure _ _)
  | (coverage_flow_head Bind.bind; apply flow_bind)
  | (coverage_flow_head ite; apply flow_ite)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
