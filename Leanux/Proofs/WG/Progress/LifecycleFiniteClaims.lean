import Leanux.Proofs.WG.Progress.LifecycleFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.LifecycleFinite
open Leanux Leanux.WG

/-- Exact finite evaluation at every native open entry, retaining errno and Stop. -/
theorem original_open_finite :
    Campaign2.AgreesOn (fun _ => True) WG.wgOpen openDevice := by
  rw [open_source]
  intro state ambient pre
  rfl

/-- Exact finite evaluation of the original native up wrapper. -/
theorem original_up_finite :
    Campaign2.AgreesOn (fun _ => True) WG.wgUp up := by
  rw [up_source]
  intro state ambient pre
  rfl

/-- Exact finite evaluation of the environment up caller. This asserts no
successful completion, queue draining, or subsequent syscall service. -/
theorem original_envUp_finite :
    Campaign2.Product.AgreesOn (fun _ => True) Env.wgUp envUp := by
  rw [envUp_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.LifecycleFinite
