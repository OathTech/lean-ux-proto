import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointSource

/-! Literal stack branch witnesses retain native route checks and the exact
routed reply call. GRO scope entry precedes each buffered entry's own bytes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "napi_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "napi_native_head " expected:ident : tactic => do
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

elab "napi_failure_head " expected:ident : tactic => do
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

macro "napi_stack_shape" : tactic => `(tactic| first
  | (napi_failure_head invariant; exact .failed (.invariant _) _)
  | (napi_failure_head unsupported; exact .failed (.unsupported _) _)
  | (napi_failure_head Stack.excluded; exact .failed (.excluded _) _)
  | (napi_native_head skipCut; exact .native .cut)
  | (napi_native_head liftRouting; exact liftedMetadataShape _ (PeerMetadata.routeAdapterShape _))
  | (napi_native_head getDev; exact liftedMetadataShape _ PeerMetadata.deviceReadShape)
  | (napi_native_head getWG; exact .native .world)
  | (napi_native_head modifyEnv; exact .native (.inbox _))
  | (napi_native_head invariant; exact .native (.invariant _))
  | (napi_native_head unsupported; exact .native (.unsupported _))
  | (napi_native_head Stack.excluded; exact .native (.excluded _))
  | (napi_shape_head liftWGObserver; exact .child (.transmit _ _ _ _))
  | (napi_shape_head Pure.pure; exact .pure _)
  | (napi_shape_head Bind.bind; apply Shape.bind)
  | (napi_shape_head ite; apply conditionalShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def reply4Shape (dst : Nat) (bytes : List UInt8) : Shape
    (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu)) dst bytes) := by
  apply Shape.marked (.reply4 dst bytes)
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' napi_stack_shape

noncomputable def receive4Shape (bytes : List UInt8) : Shape
    (receive4With (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu))) bytes) := by
  apply Shape.marked (.receive4 bytes)
  unfold receive4With
  repeat' first
    | (napi_shape_head reply4With; exact reply4Shape _ _)
    | napi_stack_shape

noncomputable def stackShape (bytes : List UInt8) : Shape (Driver.stackObserved hooks bytes) := by
  apply Shape.marked (.stack bytes)
  unfold Driver.stackObserved stackReceiveWith
  dsimp only
  split
  · exact receive4Shape bytes
  · split
    · exact .child (.receive6 bytes)
    · exact .native (.invariant _)

theorem scope_factor (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α) :
    CausalScope.prefixScope Event.scope cause body = (do
      let position ← CausalScope.enterPrefix Event.scope cause
      let value ← body ⟨position,cause⟩
      CausalScope.leavePrefix Event.scope position
      pure value) := rfl

noncomputable def taggedShape (entry : GroOccurrence.Entry) :
    Shape (hooks.stackInput entry (Driver.stackObserved hooks entry.bytes)) := by
  apply Shape.marked (.tagged entry)
  change Shape (CausalScope.prefixScope Event.scope (.stackInput entry) (fun _ => Driver.stackObserved hooks entry.bytes))
  rw [scope_factor]
  exact .bind (.native (.enter (.stackInput entry))) (fun position =>
    .bind (stackShape entry.bytes) (fun value => .bind (.native (.exit position)) (fun _ => .pure value)))

noncomputable def stackListShape (entries : List GroOccurrence.Entry) :
    Shape (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks) entries) :=
  forMShape entries _ taggedShape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
