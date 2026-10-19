import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointSource

/-! Syntactic construction of fixed helper source witnesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "consume_leaf_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "consume_leaf_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not a native lift"
  let some native := action.getAppArgs.back? | Lean.throwError "missing native action"
  let native := native.consumeMData
  let native ← if native.isAppOf ``liftWG then
      match native.getAppArgs.back? with
      | some action => pure action.consumeMData
      | none => Lean.throwError "missing WG action"
    else pure native
  let .const actual _ := native.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

elab "consume_leaf_failure_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a source bind"
  let args := action.getAppArgs
  let some body := args[args.size - 2]? | Lean.throwError "missing body"
  unless body.isAppOf ``liftPrefix do Lean.throwError "not a native failure"
  let some native := body.getAppArgs.back? | Lean.throwError "missing native action"
  let .const actual _ := native.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different failure head"

elab "consume_leaf_wg_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing WG body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
      pure body
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

elab "consume_leaf_wg_tail_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing native WG body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not native WG"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
      pure body
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not a native bind"
  let some tail := body.getAppArgs.back? | Lean.throwError "missing tail"
  let .lam _ _ tail _ := tail.consumeMData | Lean.throwError "not a lambda"
  let .const actual _ := tail.consumeMData.headBeta.getAppFn | Lean.throwError "not a tail head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different tail head"

elab "consume_leaf_wg_failure_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let args := action.getAppArgs
  let some observer := args[args.size - 2]? | Lean.throwError "missing body"
  let observer := observer.consumeMData.headBeta
  unless observer.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some body := observer.getAppArgs.back? | Lean.throwError "missing observer"
  unless body.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
  let some native := body.getAppArgs.back? | Lean.throwError "missing native action"
  let .const actual _ := native.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native failure"


theorem wg_bind (body : WG.M α) (next : α → WG.M β) :
    wg (body >>= next) = (wg body >>= fun value => wg (next value)) := by
  exact Points.wg_bind body next

theorem wg_if (test : Prop) [Decidable test] (yes no : WG.M α) :
    wg (if test then yes else no) = (if test then wg yes else wg no) := by
  split <;> rfl

noncomputable def wgBindShape (body : WG.M α) (next : α → WG.M β)
    (head : Shape (wg body)) (tail : ∀ value, Shape (wg (next value))) :
    Shape (liftWGObserver (liftWGPrefix (body >>= next))) := by
  change Shape (wg (body >>= next))
  rw [wg_bind]
  exact .bind head tail

noncomputable def wgIfShape (test : Prop) [Decidable test] (yes no : WG.M α)
    (left : test → Shape (wg yes)) (right : ¬test → Shape (wg no)) :
    Shape (liftWGObserver (liftWGPrefix (if test then yes else no))) := by
  change Shape (wg (if test then yes else no))
  rw [wg_if]
  exact conditionalShape test left right

noncomputable def wgListShape (xs : List α) (initial : σ)
    (body : α → σ → WG.M (ForInStep σ)) (shapes : ∀ item acc, Shape (wg (body item acc))) :
    Shape (wg (forIn xs initial body)) := by
  induction xs generalizing initial with
  | nil => exact .pure initial
  | cons item rest ih =>
    rw [List.forIn_cons,wg_bind]
    apply Shape.bind (shapes item initial)
    intro decision
    cases decision with
    | done final => exact .pure final
    | yield next => exact ih next

macro "consume_leaf_shape" : tactic => `(tactic| first
  | (consume_leaf_wg_failure_head invariant; exact .failed (.wgInvariant _) _)
  | (consume_leaf_wg_failure_head unsupported; exact .failed (.wgUnsupported _) _)
  | (consume_leaf_wg_head branch; exact .native (.base (.basic (.branch _ _))))
  | (consume_leaf_wg_head branchCmp; exact .native (.base (.basic (.compare _ _ _ _))))
  | (consume_leaf_wg_head getKeypair; exact .native (.base (.basic (.key _))))
  | (consume_leaf_wg_head setKeypair; exact .native (.base (.basic (.writeKey _ _))))
  | (consume_leaf_wg_head getPeer; exact .native (.base (.basic (.peer _))))
  | (consume_leaf_wg_head getDev; exact .native (.base .device))
  | (consume_leaf_wg_head get; exact .native (.base .world))
  | (consume_leaf_wg_head getAmbient; exact .native (.base (.ambient _)))
  | (consume_leaf_wg_head hidden; exact .native (.base (.ambient _)))
  | (consume_leaf_wg_head hiddenJiffies; exact .native (.base (.ambient _)))
  | (consume_leaf_wg_head refcountDecAndTest; exact .native (.base (.ambient _)))
  | (consume_leaf_wg_head invariant; exact .native (.base (.basic (.wgInvariant _))))
  | (consume_leaf_wg_head unsupported; exact .native (.base (.basic (.wgUnsupported _))))
  | (consume_leaf_wg_head Pure.pure; exact .pure _)
  | (consume_leaf_wg_head Bind.bind; apply wgBindShape)
  | (consume_leaf_wg_head ite; apply wgIfShape)
  | (consume_leaf_wg_head ForIn.forIn; apply wgListShape)
  | (consume_leaf_shape_head Bind.bind; apply Shape.bind)
  | (consume_leaf_shape_head Pure.pure; exact .pure _)
  | (consume_leaf_shape_head ite; apply conditionalShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
