import Leanux.Proofs.WG.Progress.ActivationFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ActivationFinite
open Leanux Leanux.WG

/-- Every original activation iteration has exactly this finite evaluation,
including absent-peer and unsupported-worker Stops. -/
theorem original_iteration_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.iter a) (iteration a) := by
  rw [iteration_source]
  intro w pre
  rfl

/-- Finite activation evaluation retains all native outcomes, including an
occupancy-budget exhaustion. No successful-service premise is imposed. -/
theorem original_run_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.run a) (run a) := by
  rw [run_source]
  intro w pre
  rfl

/-- Worker selection, section records, and the selected activation agree on
every entry; unavailable workers and failures remain exact. -/
theorem original_dispatch_finite (worker : Worker) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.dispatch worker) (dispatch worker) := by
  rw [dispatch_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.ActivationFinite
