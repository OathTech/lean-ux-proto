import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointGro

/-! Canonical source witness for the entire bounded RX poll. Each original
peek, queue write, candidate guard, consume, GRO and cleanup remains ordered. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "napi_wg_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some observer := action.getAppArgs.back? | Lean.throwError "missing WG observer"
  unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not a native WG lift"
  let some body := observer.getAppArgs.back? | Lean.throwError "missing native WG body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native WG head"

elab "napi_wg_tail_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
  unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not native WG"
  let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not a native bind"
  let some tail := body.getAppArgs.back? | Lean.throwError "missing tail"
  let .lam _ _ tail _ := tail.consumeMData | Lean.throwError "not a lambda"
  let .const actual _ := tail.consumeMData.headBeta.getAppFn | Lean.throwError "not a tail head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different tail head"

elab "napi_wg_failure_head " expected:ident : tactic => do
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

macro "napi_poll_shape" : tactic => `(tactic| first
  | (napi_wg_failure_head invariant; exact .failed (.wgInvariant _) _)
  | (napi_wg_failure_head unsupported; exact .failed (.wgUnsupported _) _)
  | (napi_wg_head branch; exact .native (.branch _ _))
  | (napi_wg_tail_head PrevQueue.peek; exact .native (.metadata _ (NapiMetadata.peekShape _)))
  | (napi_wg_tail_head Bind.bind; exact .native (.metadata _ (NapiMetadata.dropShape _)))
  | (napi_wg_tail_head setPeer; exact .native (.metadata _ (NapiMetadata.writePeerShape _ _ _)))
  | (napi_wg_head WG.andM; exact .native (.rx _ (NapiMetadata.readyShape _)))
  | (napi_wg_head getRxSkb; exact .native (.rx _ (NapiMetadata.packetShape _)))
  | (napi_wg_head endpointFromSkb; exact .native (.metadata _ (NapiMetadata.endpointShape _)))
  | (napi_wg_head keypairPut; exact .native (.metadata _ (NapiMetadata.keyPutShape _)))
  | (napi_wg_head freeRxSkb; exact .native (.free _))
  | (napi_wg_head invariant; exact .native (.wgInvariant _))
  | (napi_wg_head unsupported; exact .native (.wgUnsupported _))
  | (napi_shape_head Driver.Hooks.candidateEnter; exact .native (.candidate _ _))
  | (napi_shape_head Driver.Hooks.candidateLeave; exact .native (.leave _))
  | (napi_shape_head Driver.Hooks.counterCheck; exact .child (.counter _ _))
  | (napi_shape_head liftWGObserver; first | exact .child (.consume _ _ _) | exact .child (.release _))
  | (napi_shape_head GroOccurrence.receiveWith; exact groReceiveShape _ _)
  | (napi_shape_head GroOccurrence.flushAllWith; exact groFlushShape _)
  | (napi_shape_head ForIn.forIn; apply listShape)
  | (napi_shape_head Pure.pure; exact .pure _)
  | (napi_shape_head Bind.bind; apply Shape.bind)
  | (napi_shape_head ite; apply conditionalShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def pollShape (pid : PeerId) (budget : Nat) :
    Shape (Driver.nativePollObserved hooks pid budget) := by
  apply Shape.marked (.poll pid budget)
  unfold Driver.nativePollObserved RetirementSecurity.NestedPeerRelease.pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' napi_poll_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
