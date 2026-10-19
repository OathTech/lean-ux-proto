import Leanux.Proofs.WG.Progress.LifecycleEnvironmentFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.LifecycleFinite
open Leanux

/-- Exact finite evaluation of the environment down caller, preserving every
normal result and Stop. No successful drain or service claim is added. -/
theorem original_envDown_finite :
    Campaign2.Product.AgreesOn (fun _ => True) Env.wgDown envDown := by
  rw [envDown_source]
  intro state pre
  rfl


/-- Exact finite evaluation of environment deletion. Missing-device returns,
stepped-dump refusals, inline drains and final destruction failures are retained. -/
theorem original_envDelete_finite :
    Campaign2.Product.AgreesOn (fun _ => True) Env.wgDelete envDelete := by
  rw [envDelete_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.LifecycleFinite
