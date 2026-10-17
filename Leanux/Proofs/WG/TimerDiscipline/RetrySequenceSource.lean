import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceModel
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

/-- Consecutive supplied wheel-unit/send pairs. No outer selection or environment scheduling is asserted. -/
def retrySequence : List RetryUnit → M Unit
  | [] => pure ()
  | unit :: rest => do
    retryDispatch unit
    retrySequence rest

def observedRetrySteps : List RetryUnit → M (List RetrySequenceStep)
  | [] => pure []
  | unit :: rest => do
    let before ← Campaign2.Product.read
    let result ← observedRetryRearm unit
    let after ← Campaign2.Product.read
    let steps ← observedRetrySteps rest
    return ⟨unit, before, result, after⟩ :: steps

def observedRetrySequence (units : List RetryUnit) : M (Snapshot × List RetrySequenceStep) := do
  let entry ← Campaign2.Product.read
  let steps ← observedRetrySteps units
  return (entry, steps)

theorem retrySequence_read_discard {α : Type} (a : M α) :
    (do let _ ← Campaign2.Product.read; a) = a := rfl

/-- Exact equality includes the first original error; observations do not turn
failure into a returned partial list. -/
theorem observedRetrySteps_erase (units : List RetryUnit) :
    (do let _ ← observedRetrySteps units; pure ()) = retrySequence units := by
  induction units with
  | nil => rfl
  | cons unit rest ih =>
    rw [retrySequence, ← observedRetryRearm_erase, ← ih]
    simp only [observedRetrySteps, bind_assoc, pure_bind, retrySequence_read_discard]

theorem observedRetrySequence_erase (units : List RetryUnit) :
    (do let _ ← observedRetrySequence units; pure ()) = retrySequence units := by
  rw [← observedRetrySteps_erase]
  simp only [observedRetrySequence, bind_assoc, pure_bind, retrySequence_read_discard]

end Leanux.Proofs.WG.TimerDiscipline
