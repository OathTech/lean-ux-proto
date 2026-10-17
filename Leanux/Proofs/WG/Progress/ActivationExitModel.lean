import Leanux.Proofs.WG.Campaign2.ProductView

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- Actual last phase. A failure has no invented successor state. The count
records completed continuing iterations before this phase. -/
inductive ActivationExitResult (σ : Type) where
  | iterationError (continued : Nat) (active : Activation) (before : σ) (error : Stop)
  | ended (continued : Nat) (active : Activation) (before afterIteration : σ)
      (stop : Except Stop (List UInt8 × σ))
  | yielded (continued : Nat) (active : Activation) (before afterIteration final : σ)
  | exhausted (continued : Nat) (active : Activation) (before : σ) (error : Stop)

namespace ActivationExitResult

def continued {σ : Type} : ActivationExitResult σ → Nat
  | .iterationError n .. | .ended n .. | .yielded n .. | .exhausted n .. => n

def active {σ : Type} : ActivationExitResult σ → Activation
  | .iterationError _ a .. | .ended _ a .. | .yielded _ a .. | .exhausted _ a .. => a

def attempts {σ : Type} : ActivationExitResult σ → Nat
  | .iterationError n .. | .ended n .. | .yielded n .. => n + 1
  | .exhausted n .. => n

def erase {σ : Type} : ActivationExitResult σ → Except Stop (Unit × σ)
  | .iterationError _ _ _ error | .exhausted _ _ _ error => .error error
  | .ended _ _ _ _ stop => stop.map fun (_, final) => ((), final)
  | .yielded _ _ _ _ final => .ok ((), final)

def map {σ τ : Type} (project : σ → τ) : ActivationExitResult σ → ActivationExitResult τ
  | .iterationError n a before error => .iterationError n a (project before) error
  | .ended n a before middle stop => .ended n a (project before) (project middle)
      (stop.map fun (bytes, final) => (bytes, project final))
  | .yielded n a before middle final => .yielded n a (project before) (project middle) (project final)
  | .exhausted n a before error => .exhausted n a (project before) error

end ActivationExitResult

/-- Occupancy is read once from the actual entry. A failed occupancy read
precedes every iteration. -/
inductive ActivationExitAudit (σ : Type) where
  | occupancyError (error : Stop)
  | ran (occupancy : Nat) (entry : σ) (result : ActivationExitResult σ)

namespace ActivationExitAudit

def erase {σ : Type} : ActivationExitAudit σ → Except Stop (Unit × σ)
  | .occupancyError error => .error error
  | .ran _ _ result => result.erase

def map {σ τ : Type} (project : σ → τ) : ActivationExitAudit σ → ActivationExitAudit τ
  | .occupancyError error => .occupancyError error
  | .ran occupancy entry result => .ran occupancy (project entry) (result.map project)

end ActivationExitAudit

/-- Bounded outer-call accounting and the exact exit updates. No conclusion
about callback termination, sufficient fuel or global emptiness is made. -/
def ActivationExitFacts (original : Activation) :
    ActivationExitAudit Campaign2.Product.Snapshot → Prop
  | .occupancyError _ => True
  | .ran occupancy _ result =>
      result.attempts ≤ occupancy + 1 ∧
      result.active = {original with iterations := original.iterations + result.continued} ∧
      match result with
      | .yielded _ active _ middle final =>
        final = {middle with ambient := {middle.ambient with suspended :=
          middle.ambient.suspended ++ [{active with iterations := active.iterations + 1}]}}
      | .exhausted n _ _ error => n = occupancy + 1 ∧ error = .invariant
          s!"{original.worker.symbol} consumed more items than its queue held ({occupancy}) in one run"
      | _ => True

end Leanux.Proofs.WG.Progress
