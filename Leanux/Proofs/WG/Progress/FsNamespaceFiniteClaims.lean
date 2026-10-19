import Leanux.Proofs.WG.Progress.FsNamespaceFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-- Exact finite evaluation of closing the namespace holders, including every
original Stop. Later deferred namespace cleanup is a separate caller. -/
theorem original_netnsClose_finite :
    Campaign2.Product.AgreesOn (fun _ => True) Leanux.netnsClose netnsClose := by
  rw [netnsClose_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
