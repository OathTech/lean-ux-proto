import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveEnvWorkers
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Timestamp archive retention through the actual deferred source calls. Timer and
worker callbacks share one journal, including receipts retained before Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

macro "archive_driver_deferred_step " : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_native _ (fun h => frame_store h _ getDev_sameWGStore))
  | (scheduler_preserve_at delTimer; exact product_native _ (del_timer _ _))
  | (scheduler_preserve_at Env.runOneSendWorker; exact send_one)
  | (nonce_product_head Driver.Hooks.sendWorker; exact send_one)
  | (scheduler_preserve_at Env.runOneClearWorker; exact clear_one)
  | (scheduler_preserve_at Env.requireDrained; exact product_store _ (Nonce.Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact product_store _ (Nonce.Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact product_store _ (Nonce.Frames.nothing_due _))
  | (scheduler_preserve_at Driver.timerObserved; exact product_safe (timer _ _))
  | (scheduler_preserve_at throw; exact product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact PrefixPreserves.pure (fun _ _ hi => hi.1) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; first
     | apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.1)
     | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem crypt :
    PrefixPreserves ProductInv History (Driver.cryptObserved TimestampDriver.hooks) :=
  PrefixPreserves.bind (schedule none) (fun _ => product_store _ deliverSent_sameKernel)

theorem send_workers :
    PrefixPreserves ProductInv History (Driver.sendWorkersObserved TimestampDriver.hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

theorem after_xmit :
    PrefixPreserves ProductInv History (Driver.afterXmitObserved TimestampDriver.hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

theorem timer_section (worker : Worker) {body : PrefixM TimestampReceipt Unit}
    (safe : PrefixPreserves ProductInv History body) :
    PrefixPreserves ProductInv History (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      PrefixPreserves.bind (product_ambient _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.1) product_stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.1) product_stable worker safe)

theorem timers (jPass : UInt64) :
    PrefixPreserves ProductInv History (Driver.timersObserved TimestampDriver.hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_safe (timer _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

theorem placeholder_timers (jHi : UInt64) :
    PrefixPreserves ProductInv History (Driver.placeholderTimersObserved TimestampDriver.hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_safe (timer _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

theorem idle_timers :
    PrefixPreserves ProductInv History (Driver.idleTimersObserved TimestampDriver.hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

theorem after_advance :
    PrefixPreserves ProductInv History (Driver.afterAdvanceObserved TimestampDriver.hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure ())
    | archive_driver_deferred_step

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
