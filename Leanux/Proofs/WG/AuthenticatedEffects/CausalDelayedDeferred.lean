import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedDeferredFrames

/-! The actual deferred and timer loops carry the same live timer/work occurrences
through callbacks, clear work and scheduler trials. Selection validity is a
separate positional obligation, not an assumption made by these state frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
macro "causal_delayed_deferred_native" : tactic => `(tactic| first
  | (causal_delayed_product_native getWG; exact wg_read)
  | (causal_delayed_product_native getEnv; exact env_read)
  | (causal_delayed_product_native modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (causal_delayed_product_native liftWG; apply product_wg; first
      | (causal_delayed_native_head delTimer; exact delete _ _)
      | solve | causal_delayed_native)
  | (causal_delayed_product_native Env.runOneClearWorker; exact clear_one)
  | (causal_delayed_head clearWorkerObserved; exact clear_worker)
  | (causal_delayed_product_native Env.requireDrained; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.drained _ _))
  | (causal_delayed_product_native Env.requireNoCryptWork; exact product_store_lift _ requireNoCryptWork_sameKernel)
  | (causal_delayed_product_native Env.deliverSent; exact product_store_lift _ deliverSent_sameKernel)
  | (causal_delayed_product_native Env.peekNextSite; exact product_store_lift _ peekNextSite_sameKernel)
  | (causal_delayed_product_native Env.timerWorker; exact product_store_lift _ (timerWorker_sameKernel _))
  | (causal_delayed_product_native Env.requireStepComplete; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.step_complete _))
  | (causal_delayed_product_native Env.requireNothingDue; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.nothing_due _))
  | (causal_delayed_product_native throw; exact product_throw _)
  | (first | causal_delayed_product_native getAmbient | causal_delayed_product_native modifyAmbient
           | causal_delayed_product_native recordBudget | causal_delayed_product_native peekUnit
           | causal_delayed_product_native peekSiteU64 | causal_delayed_product_native hiddenJiffies
           | causal_delayed_product_native invariant | causal_delayed_product_native unsupported
           | causal_delayed_product_native budgetExhausted
     exact product_ambient _))

macro "causal_delayed_deferred_step" : tactic => `(tactic| first
  | solve | causal_delayed_deferred_native
  | (causal_delayed_head ForIn.forIn; first | apply product_range | apply product_forIn)
  | causal_delayed_product_step)

theorem deliver : ProductSafe hooks.deliver :=
  DeliverySource.observed_preserves Event.delivery (fun _ _ _ => True.intro)
    (fun _ _ _ hi => hi.append _) (product_store_lift _ deliverSent_sameKernel)

theorem crypt :
    ProductSafe (cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => deliver)

theorem sendWorkers :
    ProductSafe (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head sendWorkerObserved; exact send_worker)
    | (causal_delayed_head scheduleObserved; exact schedule _)
    | causal_delayed_deferred_step

theorem afterXmit :
    ProductSafe (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head cryptObserved; exact crypt)
    | (causal_delayed_head sendWorkersObserved; exact sendWorkers)
    | causal_delayed_deferred_step

theorem timerSection (worker : Worker) (body : PrefixM Event Unit)
    (safe : ProductSafe body) :
    ProductSafe (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact product_bind (product_ambient _) (fun _ => product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ _ => True.intro) product_store worker safe))
  · exact product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ _ => True.intro) product_store worker safe)

theorem timers (j : UInt64) :
    ProductSafe (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head sendWorkerObserved; exact send_worker)
    | (causal_delayed_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (causal_delayed_head Hooks.timerFinished; exact timer_finished _)
    | (causal_delayed_head cryptObserved; exact crypt)
    | (causal_delayed_head timerSectionObserved
       apply timerSection
       exact product_state (timer_callback _ _))
    | causal_delayed_deferred_step

theorem placeholderTimers (j : UInt64) :
    ProductSafe (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (causal_delayed_head Hooks.timerFinished; exact timer_finished _)
    | (causal_delayed_head cryptObserved; exact crypt)
    | (causal_delayed_head sendWorkersObserved; exact sendWorkers)
    | (causal_delayed_head timerSectionObserved
       apply timerSection
       exact product_state (timer_callback _ _))
    | causal_delayed_deferred_step

theorem idleTimers :
    ProductSafe (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head timersObserved; exact timers _)
    | (causal_delayed_head placeholderTimersObserved; exact placeholderTimers _)
    | causal_delayed_deferred_step

theorem afterAdvance :
    ProductSafe (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_head Hooks.deliver; exact deliver)
    | (causal_delayed_head timersObserved; exact timers _)
    | (causal_delayed_head placeholderTimersObserved; exact placeholderTimers _)
    | causal_delayed_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
