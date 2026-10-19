import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferredFrames

/-! Concrete deferred and timer source bodies compose the exact worker
contracts. The scheduler and work callbacks remain explicit until joined. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver
open CompleteProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "complete_deferred_step" : tactic => `(tactic| first
  | solve | complete_deferred_native
  | (complete_product_head ForIn.forIn; first | apply range | apply list)
  | complete_product_step)

theorem crypt (scheduled : ∀ stack, Checked (scheduleObserved hooks stack)) :
    Checked (cryptObserved hooks) :=
  bind_checked (scheduled none) (fun _ => delivery)

theorem sendWorkers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) :
    Checked (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (complete_product_head sendWorkerObserved; exact sentWork)
    | (complete_product_head scheduleObserved; exact scheduled _)
    | complete_deferred_step

theorem afterXmit (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) :
    Checked (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (complete_product_head cryptObserved; exact crypt scheduled)
    | (complete_product_head sendWorkersObserved; exact sendWorkers scheduled sentWork)
    | complete_deferred_step

theorem timerSection (worker : Worker) (body : PrefixM Event Unit)
    (safe : Checked body) :
    Checked (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact bind_checked (ambient _) (fun _ => bind_checked (ambient _) (fun _ =>
      runWorkerPrefix_preserves carrier_safe stable worker safe))
  · exact bind_checked (ambient _) (fun _ =>
      runWorkerPrefix_preserves carrier_safe stable worker safe)

theorem timers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) (j : UInt64) :
    Checked (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (complete_product_head sendWorkerObserved; exact sentWork)
    | (complete_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (complete_product_head Hooks.timerFinished; exact timer_finished _)
    | (complete_product_head cryptObserved; exact crypt scheduled)
    | (complete_product_head timerSectionObserved
       apply timerSection
       exact state (timer _ _))
    | (complete_product_head clearWorkerObserved; exact clearedWork)
    | complete_deferred_step

theorem placeholderTimers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) (j : UInt64) :
    Checked (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (complete_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (complete_product_head Hooks.timerFinished; exact timer_finished _)
    | (complete_product_head cryptObserved; exact crypt scheduled)
    | (complete_product_head sendWorkersObserved; exact sendWorkers scheduled sentWork)
    | (complete_product_head timerSectionObserved
       apply timerSection
       exact state (timer _ _))
    | (complete_product_head clearWorkerObserved; exact clearedWork)
    | complete_deferred_step

theorem idleTimers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) :
    Checked (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (complete_product_head timersObserved; exact timers scheduled sentWork clearedWork _)
    | (complete_product_head placeholderTimersObserved; exact placeholderTimers scheduled sentWork clearedWork _)
    | (complete_product_head clearWorkerObserved; exact clearedWork)
    | complete_deferred_step

theorem afterAdvance (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) :
    Checked (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (complete_product_head timersObserved; exact timers scheduled sentWork clearedWork _)
    | (complete_product_head placeholderTimersObserved; exact placeholderTimers scheduled sentWork clearedWork _)
    | (complete_product_head clearWorkerObserved; exact clearedWork)
    | complete_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Deferred
