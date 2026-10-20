import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficReadSource

/-! Canonical source witnesses expose the unchanged traffic control flow.
Lists and ranges use their original values; no independent runner is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal Driver

elab "traffic_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a traffic source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different source head"

elab "traffic_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a traffic source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not a native lift"
  let some native := action.getAppArgs.back? | Lean.throwError "missing native action"
  let native := native.consumeMData
  let native ← if native.isAppOf ``liftWG then
      match native.getAppArgs.back? with
      | some body=>pure body.consumeMData
      | none=>Lean.throwError "missing WG action"
    else pure native
  let .const actual _ := native.getAppFn | Lean.throwError "not a constant native source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different native head"

macro "traffic_shape_step" : tactic => `(tactic| first
  | (traffic_shape_head Pure.pure; exact .pure _)
  | (traffic_shape_head Bind.bind; apply Shape.bind)
  | (traffic_shape_head ite; apply conditionalShape)
  | (traffic_shape_head ForIn.forIn; first | apply rangeShape | apply listShape)
  | (traffic_shape_head receiveEntryObserved; exact .native (.receive _ _))
  | (traffic_shape_head multicastObserved; exact .native (.multicast _ _))
  | (traffic_shape_head drainObserved; exact .service (.native (.reading (ProductRead.drainedShape _ _))))
  | (traffic_shape_head inlinePollObserved; exact .poll)
  | (traffic_shape_head cryptObserved; exact .service Service.Points.cryptShape)
  | (traffic_shape_head sendWorkersObserved; exact .service (.child (.family .sends)))
  | (traffic_shape_head sendWorkerObserved; exact .service (.child (.family .sendWorker)))
  | (traffic_shape_head scheduleObserved; exact .service (.child (.family (.schedule _))))
  | (traffic_shape_head Hooks.deliver; exact .service Service.Points.deliveryShape)
  | (traffic_shape_head liftWGObserver; exact .transmit _ _ _ _)
  | (traffic_native_head getWG; exact .service (.native (.reading (.wg .read))))
  | (traffic_native_head getDev; exact .service (.native (.reading (.wg ReadAccess.deviceShape))))
  | (traffic_native_head getEnv; exact .service (.native (.reading ProductRead.environmentShape)))
  | (traffic_native_head getRouting; exact .service (.native (.reading ProductRead.routingShape)))
  | (traffic_native_head getAmbient; exact .native (.base (.ambient (get : AmbientM Ambient))))
  | (traffic_native_head modifyAmbient; exact .native (.base (.ambientEdit _)))
  | (traffic_native_head modifyWG; exact .native (.base .reset))
  | (traffic_native_head recordBudget; exact .native (.base (.ambient AmbientM.recordBudget)))
  | (traffic_native_head peekNextSite; exact .service (.native (.reading ProductRead.peekShape)))
  | (traffic_native_head hidden; exact .native (.base (.ambient (AmbientM.hidden _))))
  | (traffic_native_head invariant; exact .native (.base (.ambient (AmbientM.invariant _))))
  | (traffic_native_head unsupported; exact .native (.base (.ambient (AmbientM.unsupported _))))
  | (traffic_native_head fixtureSend; exact .native .fixture)
  | (traffic_native_head senderSource; exact .service (.native (.reading (ProductRead.senderShape _ _ _ _))))
  | (traffic_native_head xmitPackets; exact .service (.native (.reading (ProductRead.packetsShape _ _ _ _))))
  | (traffic_native_head requireNotPending; exact .native (.pending _ _))
  | (traffic_shape_head liftPrefix; exact .native (.route _))
  | maintenance_join_let
  | maintenance_join_use
  | intro value
  | (dsimp +failIfUnchanged only)
  | split)

noncomputable def workerShape (worker : Worker) (body : PrefixM Event Unit) (shape : Shape body) :
    Shape (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact shape | traffic_shape_step

noncomputable def afterBatchSource : Shape (afterBatchObserved hooks) := by
  unfold afterBatchObserved DeliverySource.afterBatchWith
  repeat' traffic_shape_step

noncomputable def receiveSource (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Shape (injectObserved hooks family port msg tos ll dest) := by
  unfold injectObserved TrafficSource.injectWith
  repeat' first
    | (traffic_shape_head runWorkerPrefix; apply workerShape)
    | traffic_shape_step

noncomputable def floodSource (count port family : Nat) (messages : List (List UInt8)) :
    Shape (floodObserved hooks count port family messages) := by
  unfold floodObserved TrafficSource.floodWith
  repeat' first
    | (traffic_shape_head runWorkerPrefix; apply workerShape)
    | (traffic_shape_head afterBatchObserved; exact afterBatchSource)
    | traffic_shape_step

noncomputable def itemSource (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    Shape (batchItemObserved hooks device cqes item) := by
  cases item
  all_goals unfold batchItemObserved batchItemWith
  all_goals repeat' first
    | (traffic_shape_head runWorkerPrefix; apply workerShape)
    | traffic_shape_step

noncomputable def batchSource (items : List Env.BatchItem) : Shape (batchObserved hooks items) := by
  unfold batchObserved TrafficSource.batchWith
  repeat' first
    | (traffic_shape_head batchItemObserved; exact itemSource _ _ _)
    | (traffic_shape_head afterBatchObserved; exact afterBatchSource)
    | traffic_shape_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
