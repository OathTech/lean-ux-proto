import Leanux.Proofs.WG.HandshakeSecurity.ExchangeControl
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverFacts
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! The same exchange ledger passes through deferred send work and both timer
modes. Timer scope tokens are observational and preserve the ledger. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

macro "exchange_driver_deferred_step " facts:term : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at getEnv; exact env_read)
  | (scheduler_preserve_at modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact product_native _ (fun h => frame_store h _ getDev_sameWGStore))
  | (scheduler_preserve_at delTimer; exact product_native _ (fun h => frame_tag h _ (($facts).handshake.deleteTimer _ _)))
  | (nonce_product_head Driver.sendWorkerObserved; exact send_one_checked ($facts).edges ($facts).handshake)
  | (scheduler_preserve_at Env.runOneClearWorker; exact product_lift _ (clear_one_frame ($facts).control))
  | (nonce_product_head Driver.clearWorkerObserved; rw [Driver.clearWorker_lift ExchangeDriver.hooks rfl]; exact product_lift _ (clear_one_frame ($facts).control))
  | (scheduler_preserve_at Env.requireDrained; exact product_store _ (Nonce.Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (nonce_product_head Driver.Hooks.deliver; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact product_store _ (Nonce.Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact product_store _ (Nonce.Frames.nothing_due _))
  | (scheduler_preserve_at Driver.timerObserved; exact product_state (timer_checked ($facts).control _ _))
  | (scheduler_preserve_at throw; exact product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; first
     | apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
     | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem crypt (facts : H1DriverSourceFacts) :
    PrefixPreserves ProductInv Safe (Driver.cryptObserved ExchangeDriver.hooks) :=
  PrefixPreserves.bind (schedule_checked facts.edges facts.handshake facts.data facts.workers none) (fun _ => product_store _ deliverSent_sameKernel)

theorem send_workers (facts : H1DriverSourceFacts) :
    PrefixPreserves ProductInv Safe (Driver.sendWorkersObserved ExchangeDriver.hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (nonce_product_head Driver.scheduleObserved; exact schedule_checked facts.edges facts.handshake facts.data facts.workers _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

theorem after_xmit (facts : H1DriverSourceFacts) :
    PrefixPreserves ProductInv Safe (Driver.afterXmitObserved ExchangeDriver.hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt facts)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers facts)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

theorem timer_section (worker : Worker) {body : PrefixM Event Unit}
    (safe : PrefixPreserves ProductInv Safe body) :
    PrefixPreserves ProductInv Safe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      PrefixPreserves.bind (product_ambient _) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.safe) product_stable worker safe))
  · exact PrefixPreserves.bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.safe) product_stable worker safe)

theorem timers (facts : H1DriverSourceFacts) (jPass : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.timersObserved ExchangeDriver.hooks jPass) := by
  unfold Driver.timersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt facts)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_state (timer_checked facts.control _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

theorem placeholder_timers (facts : H1DriverSourceFacts) (jHi : UInt64) :
    PrefixPreserves ProductInv Safe (Driver.placeholderTimersObserved ExchangeDriver.hooks jHi) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt facts)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers facts)
    | (nonce_product_head Driver.timerSectionObserved
       exact timer_section _ (product_state (timer_checked facts.control _ _)))
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

theorem idle_timers (facts : H1DriverSourceFacts) :
    PrefixPreserves ProductInv Safe (Driver.idleTimersObserved ExchangeDriver.hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers facts _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers facts _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

theorem after_advance (facts : H1DriverSourceFacts) :
    PrefixPreserves ProductInv Safe (Driver.afterAdvanceObserved ExchangeDriver.hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head Driver.timersObserved; exact timers facts _)
    | (nonce_product_head Driver.placeholderTimersObserved; exact placeholder_timers facts _)
    | (nonce_product_head Driver.Hooks.timerSelected; exact product_pure 0)
    | (nonce_product_head Driver.Hooks.timerFinished; exact product_pure ())
    | exchange_driver_deferred_step facts

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
