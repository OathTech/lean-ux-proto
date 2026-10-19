import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCarrierScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionDeferredFrames

/-! Native bookkeeping and lexical timer receipts preserve the paired
emission/delivery carrier. Native deliverSent is deliberately absent: only
the checked delivery observer may clear the pending sent buffer here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity

theorem native (action : Leanux.M α) (frame : SameView EmissionOuter.Sent action) : ProductSafe (liftPrefix action) :=
  Emissions.carrier_product_native action frame

theorem ambient (action : AmbientM α) : ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  native _ (EmissionOuter.ambient action)

theorem wg (action : WG.M α) (frame : SameView WGWorld.sent action) : ProductSafe (liftPrefix (liftWG action)) :=
  native _ (EmissionOuter.wg action frame)

theorem product_throw (stop : Stop) : ProductSafe (liftPrefix (throw stop : Leanux.M α)) :=
  product_native _ (Emissions.product_throw stop)

theorem timer_selected (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProductSafe (hooks.timerSelected d bound pid timer entry) := by
  apply product_combine _ _ (quiet_hooks.timerSelected d bound pid timer entry)
  intro w h hi
  apply Emissions.product_bind (Emissions.product_emit (.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)) rfl) _ w h hi
  intro _ w' h' hi'
  exact ⟨[.scope (.entered ⟨h'.length,.timer bound pid timer entry⟩)],rfl,True.intro,hi'.quiet _ rfl⟩

theorem timer_finished (token : Nat) : ProductSafe (hooks.timerFinished token) :=
  product_combine _ (Emissions.product_emit _ rfl) (quiet_hooks.timerFinished token)

theorem clear_worker : ProductSafe (Driver.clearWorkerObserved hooks) :=
  product_combine _
    (Emissions.product_native_callback _
      (CallbackFrames.clear_worker_quiet contributing? (fun _ => rfl))
      CallbackFrames.clear_worker_erases EmissionFrames.clear_one)
    (CallbackQuiet.product_safe (CallbackFrames.clear_worker_quiet delivery? (fun _ => rfl))
      (fun _ _ safe quiet => safe.quiet quiet))

open Lean Meta Elab Tactic in
elab "emission_carrier_native_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product emission carrier"
  let mut action := target.getAppArgs.back!.consumeMData.headBeta
  let expected := wanted.getId.eraseMacroScopes.toString
  for wrapper in [``liftWGObserver, ``liftPrefix, ``liftM, ``MonadLiftT.monadLift,
      ``MonadLift.monadLift, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString && !wrapper.toString.endsWith ("." ++ expected) then
      action := action.getAppArgs.back!.consumeMData
  let .const actual _ := action.getAppFn | throwError "not a constant-headed leaf"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different leaf"

macro "emission_deferred_native" : tactic => `(tactic| first
  | (emission_carrier_native_head getWG; exact native _ EmissionOuter.read_wg)
  | (emission_carrier_native_head getEnv; exact native _ EmissionFrames.env_read)
  | (emission_carrier_native_head modifyWG; exact native _ (EmissionFrames.wg_edit _ (fun _ => rfl)))
  | (emission_carrier_native_head liftWG; apply wg; first
      | (emission_frame_head delTimer; exact EmissionFrames.delete _ _)
      | sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec])
  | (emission_carrier_native_head Driver.clearWorkerObserved; exact clear_worker)
  | (emission_carrier_native_head Env.runOneClearWorker; exact native _ EmissionFrames.clear_one)
  | (emission_carrier_native_head Env.requireDrained; exact native _ (EmissionFrames.drained _ _))
  | (emission_carrier_native_head Env.requireNoCryptWork; exact native _ EmissionFrames.no_crypt)
  | (emission_carrier_native_head Env.peekNextSite; exact native _ EmissionFrames.peek_next)
  | (emission_carrier_native_head Env.timerWorker; exact native _ (EmissionFrames.timer_worker _))
  | (emission_carrier_native_head Env.requireStepComplete; exact native _ (EmissionFrames.step_complete _))
  | (emission_carrier_native_head Env.requireNothingDue; exact native _ (EmissionFrames.nothing_due _))
  | (emission_carrier_native_head throw; exact product_throw _)
  | ((first
       | emission_carrier_native_head getAmbient
       | emission_carrier_native_head modifyAmbient
       | emission_carrier_native_head recordBudget
       | emission_carrier_native_head peekUnit
       | emission_carrier_native_head peekSiteU64
       | emission_carrier_native_head hiddenJiffies
       | emission_carrier_native_head invariant
       | emission_carrier_native_head unsupported
       | emission_carrier_native_head budgetExhausted)
     exact ambient _))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
