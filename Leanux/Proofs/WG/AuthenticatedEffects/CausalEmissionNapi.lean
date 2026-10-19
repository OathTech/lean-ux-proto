import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionStack

/-! Direct and softirq NAPI calls retain emission occurrences through their
native scheduling choices. Worker bookkeeping is framed against sent itself. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem run_worker (worker : Worker) (body : PrefixM Event Unit) (safe : ProductSafe body) :
    ProductSafe (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first
    | exact safe
    | (emission_head liftPrefix; exact product_ambient _)
    | emission_product_step

private theorem pending : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) := by
  apply product_state
  apply state_native
  sent_frame [RxNapi.pendingSource] using []

private theorem scheduled : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) := by
  apply product_state
  apply state_native
  sent_frame [RxNapi.scheduledSource] using []

private theorem placement : ProductSafe (liftPrefix chooseNapiHere) := by
  apply product_native
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

macro "emission_napi_native" : tactic => `(tactic| first
  | (emission_product_native_head chooseNapiHere; exact placement)
  | (emission_product_native_head getAmbient; exact product_ambient (get : AmbientM Ambient))
  | (emission_product_native_head peekHiddenSite; exact product_ambient AmbientM.peekHiddenSite)
  | (emission_product_native_head unsupported; exact product_ambient (AmbientM.unsupported _))
  | (emission_product_native_head invariant; exact product_ambient (AmbientM.invariant _)))

theorem softirq : ProductSafe (Driver.softirqObserved hooks) := by
  unfold Driver.softirqObserved RxNapi.softirqWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_poll_head RxNapi.pendingSource; exact pending)
    | (emission_head liftWGObserver; exact pending)
    | (emission_head Driver.nativePollObserved; exact native_poll _ _)
    | (emission_head runWorkerPrefix; apply run_worker)
    | emission_napi_native
    | emission_product_step

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) := by
  unfold Driver.inlinePollObserved RxNapi.inlineWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head liftWGObserver; exact pending)
    | (emission_head Driver.nativePollObserved; exact native_poll _ _)
    | emission_napi_native
    | emission_product_step

theorem irq_exit : ProductSafe (Driver.irqExitObserved hooks) := by
  unfold Driver.irqExitObserved RxNapi.irqExitWith
  repeat' first
    | (emission_head liftWGObserver; exact scheduled)
    | (emission_head Driver.softirqObserved; exact softirq)
    | emission_napi_native
    | emission_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
