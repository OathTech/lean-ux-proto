import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityClearFrames
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! The actual deferred and timer loops carry the same staged-origin carrier
through callbacks, clear work and scheduler trials. Selection validity is a
separate positional obligation, not an assumption made by these state frames. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
theorem delivery : ProductSafe hooks.deliver :=
  DeliverySource.observed_preserves Event.delivery (fun _ _ before => before.2)
    (fun _ _ sent before => ⟨before.1.append (fun _ _ member => no_use (by simp only [List.mem_singleton] at member; subst_vars; rfl)),before.2.emit (quiet_event (event := .delivery sent) rfl)⟩)
    (product_store_lift _ deliverSent_sameKernel)

macro "available_deferred_native" : tactic => `(tactic| first
  | (available_origin_product_native getWG; exact wg_read)
  | (available_origin_product_native getEnv; exact env_read)
  | (available_origin_product_native modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (available_origin_product_native liftWG
     apply product_wg
     apply state_lift
     intro history
     repeat' first
       | (rx_retention_head delTimer; exact Native.delete_timer _ _)
       | staged_available_native)
  | (available_origin_product_native Env.runOneClearWorker; exact clear_one)
  | (available_origin_product_native Env.requireDrained; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.drained _ _))
  | (available_origin_product_native Env.requireNoCryptWork; exact product_store_lift _ requireNoCryptWork_sameKernel)
  | (available_origin_product_head Hooks.deliver; exact delivery)
  | (available_origin_product_native Env.deliverSent; exact product_store_lift _ deliverSent_sameKernel)
  | (available_origin_product_native Env.peekNextSite; exact product_store_lift _ peekNextSite_sameKernel)
  | (available_origin_product_native Env.timerWorker; exact product_store_lift _ (timerWorker_sameKernel _))
  | (available_origin_product_native Env.requireStepComplete; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.step_complete _))
  | (available_origin_product_native Env.requireNothingDue; exact product_store_lift _ (TransmitSecurity.Nonce.Frames.nothing_due _))
  | (available_origin_product_native throw; exact product_throw _)
  | (first | available_origin_product_native getAmbient | available_origin_product_native modifyAmbient
           | available_origin_product_native recordBudget | available_origin_product_native peekUnit
           | available_origin_product_native peekSiteU64 | available_origin_product_native hiddenJiffies
           | available_origin_product_native invariant | available_origin_product_native unsupported
           | available_origin_product_native budgetExhausted
     exact product_ambient _))

macro "available_deferred_step" : tactic => `(tactic| first
  | (available_origin_product_head clearWorkerObserved; exact clear_worker)
  | solve | available_deferred_native
  | (available_origin_product_head ForIn.forIn; first | apply product_range | apply product_forIn)
  | available_origin_product_step)

theorem crypt :
    ProductSafe (cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => delivery)

theorem sendWorkers :
    ProductSafe (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (available_origin_product_head sendWorkerObserved; exact send_worker)
    | (available_origin_product_head scheduleObserved; exact schedule _)
    | available_deferred_step

theorem afterXmit :
    ProductSafe (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (available_origin_product_head cryptObserved; exact crypt)
    | (available_origin_product_head sendWorkersObserved; exact sendWorkers)
    | available_deferred_step

theorem timerSection (worker : Worker) (body : PrefixM Event Unit)
    (safe : ProductSafe body) :
    ProductSafe (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact product_bind (product_ambient _) (fun _ => product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ before => before.2) product_stable worker safe))
  · exact product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ before => before.2) product_stable worker safe)

theorem timers (j : UInt64) :
    ProductSafe (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (available_origin_product_head sendWorkerObserved; exact send_worker)
    | (available_origin_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (available_origin_product_head Hooks.timerFinished; exact timer_finished _)
    | (available_origin_product_head cryptObserved; exact crypt)
    | (available_origin_product_head timerSectionObserved
       apply timerSection
       exact product_state (timer _ _))
    | available_deferred_step

theorem placeholderTimers (j : UInt64) :
    ProductSafe (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (available_origin_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (available_origin_product_head Hooks.timerFinished; exact timer_finished _)
    | (available_origin_product_head cryptObserved; exact crypt)
    | (available_origin_product_head sendWorkersObserved; exact sendWorkers)
    | (available_origin_product_head timerSectionObserved
       apply timerSection
       exact product_state (timer _ _))
    | available_deferred_step

theorem idleTimers :
    ProductSafe (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (available_origin_product_head timersObserved; exact timers _)
    | (available_origin_product_head placeholderTimersObserved; exact placeholderTimers _)
    | available_deferred_step

theorem afterAdvance :
    ProductSafe (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (available_origin_product_head timersObserved; exact timers _)
    | (available_origin_product_head placeholderTimersObserved; exact placeholderTimers _)
    | available_deferred_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
