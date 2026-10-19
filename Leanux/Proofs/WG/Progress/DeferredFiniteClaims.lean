import Leanux.Proofs.WG.Progress.DeferredFiniteSource
import Leanux.Proofs.WG.Progress.DeferredFiniteNativeClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes

/-- Exact finite evaluation for every deferred constructor and every entry.
This retains native budgets and exhaustion; it does not assert useful service. -/
theorem DeferredFinite.original_evaluate_finite (call : EnvDeferredCall) :
    Campaign2.Product.AgreesOn (fun _=>True) call.original (DeferredFinite.evaluate call) := by
  rw [DeferredFinite.evaluate_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress
