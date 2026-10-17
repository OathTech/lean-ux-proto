import Leanux.Proofs.WG.Progress.ActivationExitSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Actual observed activation exits obey the captured bound and retain the
real activation counter and suspension append in every record mode. -/
theorem observedActivationExit_facts (a : Activation) :
    Campaign2.Product.Returns (observedActivationExit a) (fun _ => True)
      (fun audit _ => ActivationExitFacts a audit) := by
  intro entry _
  exact ⟨_, entry, rfl, activationExitRun_facts a entry⟩

end Leanux.Proofs.WG.Progress
