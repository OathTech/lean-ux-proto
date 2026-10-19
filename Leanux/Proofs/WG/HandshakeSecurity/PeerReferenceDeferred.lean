import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceSend
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Positive-reference entry certificates through deferred source calls, including
actual queued sends and timer callbacks before later Stop. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

macro "peer_reference_driver_deferred_step " : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_native _ (store getDev_sameWGStore))
  | (scheduler_preserve_at delTimer; exact product_native _ (del_timer _ _))
  | (scheduler_preserve_at Env.runOneSendWorker; exact native_send_one_observed)
  | (nonce_product_head Driver.sendWorkerObserved; exact send_one)
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
    PrefixPreserves ProductInv Safe (Driver.cryptObserved ExchangeDriver.hooks) :=
  PrefixPreserves.bind (schedule none) (fun _ => product_store _ deliverSent_sameKernel)

theorem send_workers :
    PrefixPreserves ProductInv Safe (Driver.sendWorkersObserved ExchangeDriver.hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

theorem after_xmit :
    PrefixPreserves ProductInv Safe (Driver.afterXmitObserved ExchangeDriver.hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

theorem timer_section (worker : Worker) {body : PrefixM Exchange.Event Unit}
    (safe : PrefixPreserves ProductInv Safe body) :
    PrefixPreserves ProductInv Safe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      PrefixPreserves.bind (product_ambient _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.1) product_stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.1) product_stable worker safe)

theorem timers (jPass : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.timersObserved ExchangeDriver.hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_safe (timer _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

theorem placeholder_timers (jHi : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.placeholderTimersObserved ExchangeDriver.hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_safe (timer _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

theorem idle_timers :
    PrefixPreserves ProductInv Safe (Driver.idleTimersObserved ExchangeDriver.hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

theorem after_advance :
    PrefixPreserves ProductInv Safe (Driver.afterAdvanceObserved ExchangeDriver.hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | peer_reference_driver_deferred_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
