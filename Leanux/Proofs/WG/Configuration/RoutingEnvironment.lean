import Leanux.Proofs.WG.Configuration.RoutingCallers
import Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames

/-! The original activation and scheduler observers preserve routing at every
captured consume position. Copied consistency trials remain behind their actual
audit event and do not become committed consume entries. -/
namespace Leanux.Proofs.WG.RoutingPosition.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues AllowedIps Origins RoutingPosition.Callers

private theorem store_frame (a : Leanux.M α) (frame : SameProductStore a) :
    ProductRetainsRoutingCall a := ProjectedRetainsRoutingCall.of_same
      (routing_kernel (project := World.wg) a (frame.of_factor
        (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl)))

private theorem mixed_store (initial : FlatTable × FlatTable) (g : PrefixM LifetimeEvent α)
    (a : Leanux.M α) (erases : ErasesPrefix g a) (frame : SameProductStore a) :
    Focused initial (RxHistory.mixed g) := mixed initial g a erases (store_frame a frame)

private theorem filter (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.audit consistentFilterAudit) := by
  apply audit initial _ _ consistentFilterAudit_erases
  apply store_frame
  exact SameView.bind (fun state => productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi))
    (fun a => filterM_sameKernel productStoreView _ activationConsistent_sameKernel a.suspended)

private theorem pending (initial : FlatTable × FlatTable) (next : Option Nat) :
    Focused initial (RxHistory.mixed (pendingNapiPrefix next)) := by
  apply mixed_store initial _ _ (pendingNapiPrefix_erases next)
  unfold pendingNapi
  exact SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore) (fun _ => SameView.pure _ _)

private theorem txGetter (initial : FlatTable × FlatTable) (id : SkbId) :
    Focused initial (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) := by
  apply native_mixed initial _ _ (getTxSkbPrefix_erases id)
  apply ProjectedRetainsRoutingCall.of_same
  unfold getTxSkb
  exact (pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingCallers.«0».Leanux.Proofs.WG.RoutingPosition.Callers.packets_routing) (SkbStore.getTx id)

open Lean Meta Elab Tactic in
elab "routing_env_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do
    throwError "not a routing focus"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData |>.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  for _ in [0:7] do
    if action.getAppFn.constName? == some expected then return
    let some head := action.getAppFn.constName? | throwError "not a constant source head"
    unless [``RxHistory.mixed,``liftWGObserver,``liftWGPrefix,``liftPrefix,``liftWG].contains head do
      throwError "different observer head"
    let parts := action.getAppArgs
    unless parts.size > 0 do throwError "missing wrapped observer"
    action := parts.back!.consumeMData |>.headBeta
  throwError "too many source wrappers"

macro "routing_env_steps " initial:term : tactic => `(tactic| first
  | (routing_env_at HistoryAdapters.receiveIteration; exact Callers.receiveIteration $initial)
  | (routing_env_at getPeerMixed
     exact native_mixed $initial _ _ (getPeerMixed_erases _)
       (ProjectedRetainsRoutingCall.of_same (getPeer_routing _)))
  | (routing_env_at getTxSkbPrefix; exact txGetter $initial _)
  | (routing_env_at activationRefillsPrefix
     exact mixed_store $initial _ _ activationRefillsPrefix_erases activationRefills_sameKernel)
  | (routing_env_at Env.pendingDevice; exact store $initial _ (pendingDevice_sameKernel _ _))
  | (routing_env_at activationOccupancyPrefix
     exact mixed_store $initial _ _ (activationOccupancyPrefix_erases _) (activationOccupancy_sameKernel _))
  | (routing_env_at activationHasWorkPrefix
     exact mixed_store $initial _ _ (activationHasWorkPrefix_erases _) (activationHasWork_sameKernel _))
  | (routing_env_at pendingNapiPrefix; exact pending $initial _)
  | (routing_env_at txIterPrefix
     exact mixed $initial _ _ (txIterPrefix_erases _ (erasesPrefix_lift _)) (actualTxIter_routing _))
  | (routing_env_at liftWGPrefix
     apply native_mixed $initial _ _ (erasesStatePrefix_lift _)
     exact ProjectedRetainsRoutingCall.of_same (modifyDev_routing _ (fun _ => rfl)))
  | (routing_env_at getDev; exact store $initial _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  | (routing_env_at liftPrefix
     first
     | apply mixed_store $initial _ _ (erasesPrefix_lift _)
     | apply store $initial
     simp only [getAmbient,hidden,peekHiddenSite,recordBudget,budgetExhausted,peekUnit,
       resolveUnit,modifyAmbient,invariant,unsupported]
     intro state
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (routing_env_at throw
     exact mixed_store $initial _ _ (erasesPrefix_throw _) (fun _ => hoare_throw _))
  | routing_call_steps $initial)

theorem cryptAhead (initial : FlatTable × FlatTable) (pid : PeerId) :
    Focused initial (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first
    | (routing_env_at RxHistory.encryptIteration; exact Callers.encryptIteration initial)
    | routing_env_steps initial

theorem activationIteration (initial : FlatTable × FlatTable) (a : Activation) :
    Focused initial (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | (routing_env_at RxHistory.encryptIteration; exact Callers.encryptIteration initial)
    | (routing_env_at RxHistory.decryptIteration; exact Callers.decryptIteration initial)
    | (routing_env_at RxHistory.cryptAhead; exact cryptAhead initial _)
    | routing_env_steps initial

theorem activationRun (initial : FlatTable × FlatTable) (a : Activation) :
    Focused initial (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first
    | (routing_env_at RxHistory.activationIteration; exact activationIteration initial _)
    | routing_env_steps initial

theorem dispatch (initial : FlatTable × FlatTable) (worker : Worker) :
    Focused initial (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first
    | (routing_env_at RxHistory.activationRun; exact activationRun initial _)
    | routing_env_steps initial

theorem schedule (initial : FlatTable × FlatTable) (stack : Option Worker) :
    Focused initial (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (routing_env_at RxHistory.dispatch; exact dispatch initial _)
    | (routing_env_at RxHistory.activationRun; exact activationRun initial _)
    | (routing_env_at RxHistory.napiSoftirq; exact Callers.napiSoftirq initial)
    | (routing_env_at RxHistory.audit; exact filter initial)
    | routing_env_steps initial

theorem nestedResched (initial : FlatTable × FlatTable) (self : Worker) :
    Focused initial (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply bind initial _ _ (store initial _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule initial _
  · exact pure initial _

end Leanux.Proofs.WG.RoutingPosition.Environment
