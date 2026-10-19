import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointServices

/-! The native bounded workqueue drain keeps its original range, early exits,
record-selected peers and placeholder order. Each iteration is expanded. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal RetirementSecurity

elab "work_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "work_wg_head " expected:ident : tactic => do
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


elab "work_state_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not WG observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not constant head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different state head"

noncomputable def stateListShape (xs : List α) (initial : σ)
    (body : α → σ → WGPrefix Event (ForInStep σ))
    (shapes : ∀ item acc, Shape (liftWGObserver (body item acc))) :
    Shape (liftWGObserver (forIn xs initial body)) := by
  induction xs generalizing initial with
  | nil => exact .pure initial
  | cons item rest ih =>
    rw [List.forIn_cons,liftWGObserver_bind]
    apply Shape.bind (shapes item initial)
    intro decision
    cases decision with
    | done final => exact .pure final
    | yield next => exact ih next

noncomputable def stateRangeShape (range : Std.Legacy.Range) (initial : σ)
    (body : Nat → σ → WGPrefix Event (ForInStep σ))
    (shapes : ∀ item acc, Shape (liftWGObserver (body item acc))) :
    Shape (liftWGObserver (forIn range initial body)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact stateListShape _ initial body shapes

noncomputable def stateIfShape (test : Prop) [Decidable test] (yes no : WGPrefix Event α)
    (left : test → Shape (liftWGObserver yes)) (right : ¬test → Shape (liftWGObserver no)) :
    Shape (liftWGObserver (if test then yes else no)) := by
  split
  · exact left ‹_›
  · exact right ‹_›

macro "work_drain_step" : tactic => `(tactic| first
  | (work_state_head Driver.Hooks.flushedSend; exact .child (.flushedSend _))
  | (work_state_head NestedPeerRelease.flushedClearWith; exact flushedClearShape _)
  | (work_wg_head getDev; exact .leaf (.native (.base .device)))
  | (work_wg_head getAmbient; exact .leaf (.native (.base (.ambient _))))
  | (work_wg_head peekUnit; exact .leaf (.native (.base (.ambient _))))
  | (work_wg_head resolveUnit; exact .leaf (.native (.base (.ambient _))))
  | (work_wg_head «throw»; exact .leaf (.native (.failure _)))
  | (work_wg_head invariant; exact .leaf (.native (.base (.basic (.wgInvariant _)))))
  | (work_state_head ForIn.forIn; apply stateRangeShape)
  | (work_state_head Bind.bind; apply stateBindShape)
  | (work_state_head ite; apply stateIfShape)
  | (work_state_head Pure.pure; exact .pure _)
  | (work_shape_head Bind.bind; apply Shape.bind)
  | (work_shape_head Pure.pure; exact .pure _)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def drainShape (upTo : Option PeerId) :
    Shape (liftWGObserver (Driver.sendDrainObserved hooks upTo)) := by
  apply Shape.marked (.drain upTo)
  unfold Driver.sendDrainObserved HandshakeSecurity.SendExchange.drainWith
  repeat' work_drain_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
