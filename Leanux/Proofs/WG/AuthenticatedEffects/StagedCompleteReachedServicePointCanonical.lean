import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointSource

/-! Each canonical witness is built from the literal service body and its
actual original range/list. The declarations retain source branch order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal Driver
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

elab "service_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "service_native_head " expected:ident : tactic => do
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


macro "service_shape_step" : tactic => `(tactic| first
  | (service_shape_head Pure.pure; exact .pure _)
  | (service_shape_head Bind.bind; apply Shape.bind)
  | (service_shape_head ForIn.forIn; first | apply rangeShape | apply listShape)
  | (service_native_head getWG; exact .native (.kind .wg))
  | (service_native_head getDev; exact .native (.kind .device))
  | (service_native_head getEnv; exact .native (.kind .env))
  | (service_native_head getRouting; exact .native (.kind .routing))
  | (service_native_head modifyEnv; exact .native (.kind (.envEdit _)))
  | (service_native_head modifyAmbient; exact .native (.kind (.ambientEdit _)))
  | (service_native_head modifyWG; first
      | exact .native (.kind .reset) | exact .native (.kind .sentClear)
      | exact .native (.kind (.pass _)) | exact .native (.kind (.jiffies _)))
  | (service_native_head delTimer; exact .native (.kind (.delete _ _)))
  | (service_native_head Env.peekNextSite; exact .native (.kind .peek))
  | (service_native_head Env.timerWorker; exact .native (.kind (.timerWorker _)))
  | (service_native_head Env.requireStepComplete; exact .native (.kind (.stepComplete _)))
  | (service_native_head Env.requireNothingDue; exact .native (.kind (.nothingDue _)))
  | (service_native_head getAmbient; exact .native (.kind (.ambient (get : AmbientM Ambient))))
  | (service_native_head recordBudget; exact .native (.kind (.ambient AmbientM.recordBudget)))
  | (service_native_head peekUnit; exact .native (.kind (.ambient (AmbientM.peekUnit _))))
  | (service_native_head peekSiteU64; exact .native (.kind (.ambient (AmbientM.peekSiteU64 _))))
  | (service_native_head hiddenJiffies; exact .native (.kind (.ambient (AmbientM.hiddenJiffies _))))
  | (service_native_head hidden; exact .native (.kind (.ambient (AmbientM.hidden _))))
  | (service_native_head invariant; exact .native (.kind (.ambient (AmbientM.invariant (α := Unit) _))))
  | (service_native_head unsupported; exact .native (.kind (.ambient (AmbientM.unsupported (α := Unit) _))))
  | (service_native_head throw; exact .native (.kind (.ambient (throw _ : AmbientM Unit))))
  | (simp +failIfUnchanged only [lift_bind,lift_pure,lift_list])
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def deliveryShape : Shape hooks.deliver := by
  apply Shape.marked .delivery
  unfold Hooks.deliver CausalJournal.hooks DeliverySource.observed
  apply Shape.bind (.native (.kind .wg))
  intro saved
  apply Shape.bind (.native (.kind (.delivery saved.sent)))
  intro _
  unfold Env.deliverSent
  simp only [lift_bind,lift_list]
  repeat' first
    | (service_shape_head ForIn.forIn; apply listShape; intro dg acc; apply Shape.marked (.datagram dg))
    | service_shape_step

noncomputable def cryptShape : Shape (cryptObserved hooks) :=
  .marked .crypt (.bind (.child (.family (.schedule none))) (fun _ => deliveryShape))

noncomputable def timerSectionShape (worker : Worker) (body : PrefixM Event Unit)
    (shape : Shape body) : Shape (timerSectionObserved worker body) := by
  apply Shape.marked (.timerSection worker)
  unfold timerSectionObserved runWorkerPrefix
  repeat' first | exact shape | service_shape_step

noncomputable def timersShape (bound : UInt64) : Shape (timersObserved hooks bound) := by
  apply Shape.marked (.timers bound)
  unfold timersObserved
  repeat' first
    | (service_shape_head Hooks.timerSelected; exact .child (.family (.selected _ _ _ _ _)))
    | (service_shape_head Hooks.timerFinished; exact .child (.family (.finished _)))
    | (service_shape_head sendWorkerObserved; exact .child (.family .sendWorker))
    | (service_shape_head clearWorkerObserved; exact .child (.family .clearWorker))
    | (service_shape_head cryptObserved; exact cryptShape)
    | (service_shape_head Hooks.deliver; exact deliveryShape)
    | (service_shape_head timerSectionObserved; apply timerSectionShape; exact .child (.family (.timer _ _)))
    | service_shape_step

noncomputable def placeholderShape (bound : UInt64) : Shape (placeholderTimersObserved hooks bound) := by
  apply Shape.marked (.placeholders bound)
  unfold placeholderTimersObserved
  repeat' first
    | (service_shape_head Hooks.timerSelected; exact .child (.family (.selected _ _ _ _ _)))
    | (service_shape_head Hooks.timerFinished; exact .child (.family (.finished _)))
    | (service_shape_head sendWorkersObserved; exact .child (.family .sends))
    | (service_shape_head clearWorkerObserved; exact .child (.family .clearWorker))
    | (service_shape_head cryptObserved; exact cryptShape)
    | (service_shape_head timerSectionObserved; apply timerSectionShape; exact .child (.family (.timer _ _)))
    | service_shape_step

noncomputable def idleShape : Shape (idleTimersObserved hooks) := by
  apply Shape.marked .idle
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (service_shape_head timersObserved; exact timersShape _)
    | (service_shape_head placeholderTimersObserved; exact placeholderShape _)
    | service_shape_step

noncomputable def advanceShape : Shape (afterAdvanceObserved hooks) := by
  apply Shape.marked .advance
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (service_shape_head timersObserved; exact timersShape _)
    | (service_shape_head placeholderTimersObserved; exact placeholderShape _)
    | service_shape_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
