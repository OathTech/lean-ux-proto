import Leanux.Proofs.WG.TransmitSecurity.NonceDeferred
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Non-reuse through the actual deferred source calls. Wheel bookkeeping
retains the journal; all timer and scheduler callbacks use their native
observers, including failure prefixes. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "nonce_deferred_step" : tactic => `(tactic| first
  | (scheduler_preserve_at getWG; exact Frames.wg_read)
  | (scheduler_preserve_at getEnv; exact Frames.env_read)
  | (scheduler_preserve_at modifyWG; apply Frames.wg_bookkeeping; intro w; rfl)
  | (scheduler_preserve_at getDev; exact Frames.product_frame Frames.device_read)
  | (scheduler_preserve_at delTimer; exact Frames.product_frame (Frames.timer_delete _ _))
  | (scheduler_preserve_at Env.runOneSendWorker; exact Frames.product_lift Frames.one_send)
  | (scheduler_preserve_at Env.runOneClearWorker; exact Frames.product_lift Frames.one_clear)
  | (scheduler_preserve_at Env.requireDrained; exact Frames.stored (Frames.drained _ _))
  | (scheduler_preserve_at Env.requireNoCryptWork; exact Frames.stored requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.deliverSent; exact Frames.stored deliverSent_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite; exact Frames.stored peekNextSite_sameKernel)
  | (scheduler_preserve_at Env.timerWorker; exact Frames.stored (timerWorker_sameKernel _))
  | (scheduler_preserve_at Env.requireStepComplete; exact Frames.stored (Frames.step_complete _))
  | (scheduler_preserve_at Env.requireNothingDue; exact Frames.stored (Frames.nothing_due _))
  | (scheduler_preserve_at timerObserved; exact (timerObserved_safe _ _).liftWGObserver)
  | (scheduler_preserve_at throw; exact Frames.product_stop _)
  | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
           | scheduler_preserve_at recordBudget | scheduler_preserve_at peekUnit
           | scheduler_preserve_at peekSiteU64 | scheduler_preserve_at hiddenJiffies
           | scheduler_preserve_at invariant | scheduler_preserve_at unsupported
           | scheduler_preserve_at budgetExhausted
     exact Frames.product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; first
     | apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.nodup)
     | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.nodup))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem cryptObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup cryptObserved :=
  PrefixPreserves.bind (scheduleObserved_safe none) (fun _ => Frames.stored deliverSent_sameKernel)

theorem sendWorkersObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup sendWorkersObserved := by
  unfold sendWorkersObserved
  repeat' first
    | (nonce_product_head scheduleObserved; exact scheduleObserved_safe _)
    | nonce_deferred_step

theorem afterXmitObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup afterXmitObserved := by
  unfold afterXmitObserved
  repeat' first
    | (nonce_product_head cryptObserved; exact cryptObserved_safe)
    | (nonce_product_head sendWorkersObserved; exact sendWorkersObserved_safe)
    | nonce_deferred_step

theorem timerSectionObserved_safe (worker : Worker) {body : PrefixM Allocation Unit}
    (safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup body) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  repeat' first
    | (nonce_product_head runWorkerPrefix
       exact runWorkerPrefix_preserves (fun _ _ hi => hi.nodup) Frames.product_store worker safe)
    | nonce_deferred_step

theorem timersObserved_safe (jPass : UInt64) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (timersObserved jPass) := by
  unfold timersObserved
  repeat' first
    | (nonce_product_head cryptObserved; exact cryptObserved_safe)
    | (nonce_product_head timerSectionObserved
       exact timerSectionObserved_safe _ (timerObserved_safe _ _).liftWGObserver)
    | nonce_deferred_step

theorem placeholderTimersObserved_safe (jHi : UInt64) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (placeholderTimersObserved jHi) := by
  unfold placeholderTimersObserved
  repeat' first
    | (nonce_product_head cryptObserved; exact cryptObserved_safe)
    | (nonce_product_head sendWorkersObserved; exact sendWorkersObserved_safe)
    | (nonce_product_head timerSectionObserved
       exact timerSectionObserved_safe _ (timerObserved_safe _ _).liftWGObserver)
    | nonce_deferred_step

theorem idleTimersObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup idleTimersObserved := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head timersObserved; exact timersObserved_safe _)
    | (nonce_product_head placeholderTimersObserved; exact placeholderTimersObserved_safe _)
    | nonce_deferred_step

theorem afterAdvanceObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup afterAdvanceObserved := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_product_head timersObserved; exact timersObserved_safe _)
    | (nonce_product_head placeholderTimersObserved; exact placeholderTimersObserved_safe _)
    | nonce_deferred_step

end Leanux.Proofs.WG.TransmitSecurity.Nonce
