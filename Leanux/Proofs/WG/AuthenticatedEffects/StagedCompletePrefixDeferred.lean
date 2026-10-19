import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeferredFrames

/-! Deferred and timer source bodies compose full logical-prefix contracts.
Scheduler, send/clear and timer callbacks remain explicit inputs until their
concrete source-prefix proofs are joined. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver
open CompletePrefix.Product
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "prefix_deferred_step" : tactic => `(tactic| first
  | solve | prefix_deferred_native
  | (prefix_product_head ForIn.forIn; first | apply range | apply list)
  | prefix_product_step)

theorem crypt (scheduled : ∀ stack, Checked (scheduleObserved hooks stack)) :
    Checked (cryptObserved hooks) :=
  bind_checked (scheduled none) (fun _ => delivery)

theorem sendWorkers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) :
    Checked (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (prefix_product_head sendWorkerObserved; exact sentWork)
    | (prefix_product_head scheduleObserved; exact scheduled _)
    | prefix_deferred_step

theorem afterXmit (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) :
    Checked (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (prefix_product_head cryptObserved; exact crypt scheduled)
    | (prefix_product_head sendWorkersObserved; exact sendWorkers scheduled sentWork)
    | prefix_deferred_step

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

variable (timerProof : ∀ pid timer, StateChecked (Driver.timerObserved hooks pid timer))
include timerProof in

theorem timers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) (j : UInt64) :
    Checked (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (prefix_product_head sendWorkerObserved; exact sentWork)
    | (prefix_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (prefix_product_head Hooks.timerFinished; exact timer_finished _)
    | (prefix_product_head cryptObserved; exact crypt scheduled)
    | (prefix_product_head timerSectionObserved
       apply timerSection
       exact state (timerProof _ _))
    | (prefix_product_head clearWorkerObserved; exact clearedWork)
    | prefix_deferred_step

include timerProof in
theorem placeholderTimers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) (j : UInt64) :
    Checked (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (prefix_product_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (prefix_product_head Hooks.timerFinished; exact timer_finished _)
    | (prefix_product_head cryptObserved; exact crypt scheduled)
    | (prefix_product_head sendWorkersObserved; exact sendWorkers scheduled sentWork)
    | (prefix_product_head timerSectionObserved
       apply timerSection
       exact state (timerProof _ _))
    | (prefix_product_head clearWorkerObserved; exact clearedWork)
    | prefix_deferred_step

include timerProof in
theorem idleTimers (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) :
    Checked (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (prefix_product_head timersObserved; exact timers timerProof scheduled sentWork clearedWork _)
    | (prefix_product_head placeholderTimersObserved; exact placeholderTimers timerProof scheduled sentWork clearedWork _)
    | (prefix_product_head clearWorkerObserved; exact clearedWork)
    | prefix_deferred_step

include timerProof in
theorem afterAdvance (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
    (sentWork : Checked (sendWorkerObserved hooks)) (clearedWork : Checked (clearWorkerObserved hooks)) :
    Checked (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (prefix_product_head timersObserved; exact timers timerProof scheduled sentWork clearedWork _)
    | (prefix_product_head placeholderTimersObserved; exact placeholderTimers timerProof scheduled sentWork clearedWork _)
    | (prefix_product_head clearWorkerObserved; exact clearedWork)
    | prefix_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Deferred
