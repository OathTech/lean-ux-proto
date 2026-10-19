import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTimers
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Deferred dispatch carries allocation-stamped sending material through the
actual timer and worker callbacks, retaining receipts before later Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity Responder

macro "resident_deferred_step" : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_native _ (fun _ => NativeFrames.store getDev_sameWGStore) (bounds_store getDev_sameWGStore))
  | (scheduler_preserve_at delTimer; exact product_native _ (fun _ => NativeFrames.del _ _) (bounds_forget (DriverCuts.carrier_delete_timer _ _)))
  | (scheduler_preserve_at Env.runOneSendWorker; exact send_one_carrier)
  | (nonce_product_head Driver.sendWorkerObserved
     rw [Driver.sendWorker_lift _ rfl]
     exact send_one_carrier)
  | (scheduler_preserve_at Env.runOneClearWorker; exact clear_one_carrier)
  | (scheduler_preserve_at Env.requireDrained; exact product_store _ (Nonce.Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact product_store _ (Nonce.Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact product_store _ (Nonce.Frames.nothing_due _))
  | (scheduler_preserve_at Driver.timerObserved; exact product_state (timer_carrier _ _))
  | (scheduler_preserve_at throw; exact product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact PrefixPreserves.pure (fun _ _ hi => hi.1.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; first
     | apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.1.2)
     | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1.2))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem crypt_carrier :
    PrefixPreserves ProductInv Safe (Driver.cryptObserved Journal.hooks) :=
  PrefixPreserves.bind (schedule_carrier none) (fun _ => product_store _ deliverSent_sameKernel)

theorem send_workers_carrier :
    PrefixPreserves ProductInv Safe (Driver.sendWorkersObserved Journal.hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule_carrier _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

theorem after_xmit_carrier :
    PrefixPreserves ProductInv Safe (Driver.afterXmitObserved Journal.hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt_carrier)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers_carrier)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

theorem timer_section_carrier (worker : Worker) {body : PrefixM Journal.Event Unit}
    (safe : PrefixPreserves ProductInv Safe body) :
    PrefixPreserves ProductInv Safe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      PrefixPreserves.bind (product_ambient _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.1.2) product_stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.1.2) product_stable worker safe)

theorem timers_carrier (jPass : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.timersObserved Journal.hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt_carrier)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section_carrier _ (product_state (timer_carrier _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

theorem placeholder_timers_carrier (jHi : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.placeholderTimersObserved Journal.hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt_carrier)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers_carrier)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section_carrier _ (product_state (timer_carrier _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

theorem idle_timers_carrier :
    PrefixPreserves ProductInv Safe (Driver.idleTimersObserved Journal.hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers_carrier _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers_carrier _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

theorem after_advance_carrier :
    PrefixPreserves ProductInv Safe (Driver.afterAdvanceObserved Journal.hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers_carrier _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers_carrier _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact timer_selected_carrier _ _ _ _ _)
    | (nonce_product_head Driver.Hooks.timerFinished; exact timer_finished_carrier _)
    | resident_deferred_step

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
