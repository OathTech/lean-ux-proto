import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Proofs.WG.Noise

/-- Exact projected outcomes of the original native allocation consumer and
its finite outer evaluator, including Stops. This is no callback-termination
claim and requires no input readiness or successful allocation. -/
theorem hiddenAlloc_finite_agrees (site : AllocSite) :
    Campaign2.AgreesOn (fun _ => True) (hiddenAlloc site : WG.M Bool)
      (monadLift (hiddenAllocFinite site) : WG.M Bool) := by
  have source : (hiddenAlloc site : WG.M Bool) =
      (monadLift (hiddenAllocFinite site) : WG.M Bool) := by
    change (monadLift (AmbientM.hiddenAlloc site) : WG.M Bool) = _
    rw [hiddenAlloc_finite_source]
  rw [source]
  intro g ambient _
  rfl

end Leanux.Proofs.WG.Progress
