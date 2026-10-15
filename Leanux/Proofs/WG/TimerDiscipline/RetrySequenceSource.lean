import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceModel
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Consecutive original pairs only: no environment scheduling is inserted. -/
def retrySequence : List UInt64 → M Unit
  | [] => pure ()
  | horizon :: rest => do
    retryDispatch horizon
    retrySequence rest

def observedRetrySteps : List UInt64 → M (List RetrySequenceStep)
  | [] => pure []
  | horizon :: rest => do
    let before ← Campaign2.read
    let result ← observedRetryRearm horizon
    let after ← Campaign2.read
    let steps ← observedRetrySteps rest
    return ⟨horizon, before, result, after⟩ :: steps

def observedRetrySequence (horizons : List UInt64) : M (Snapshot × List RetrySequenceStep) := do
  let entry ← Campaign2.read
  let steps ← observedRetrySteps horizons
  return (entry, steps)

theorem retrySequence_read_discard {α : Type} (a : M α) :
    (do let _ ← Campaign2.read; a) = a := rfl

/-- Exact equality includes the first original error; observations do not turn
failure into a returned partial list. -/
theorem observedRetrySteps_erase (horizons : List UInt64) :
    (do let _ ← observedRetrySteps horizons; pure ()) = retrySequence horizons := by
  induction horizons with
  | nil => rfl
  | cons horizon rest ih =>
    rw [retrySequence, ← observedRetryRearm_erase, ← ih]
    simp only [observedRetrySteps, bind_assoc, pure_bind, retrySequence_read_discard]

theorem observedRetrySequence_erase (horizons : List UInt64) :
    (do let _ ← observedRetrySequence horizons; pure ()) = retrySequence horizons := by
  rw [← observedRetrySteps_erase]
  simp only [observedRetrySequence, bind_assoc, pure_bind, retrySequence_read_discard]

end Leanux.Proofs.WG.TimerDiscipline
