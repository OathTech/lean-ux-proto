import Leanux.WG.Types

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Stored fields used by allowed-IP dump sizing and serialization. Ownership,
parent links and children are intentionally absent. -/
def dumpNodeView (n : AipNode) : Nat × Nat × Nat :=
  (n.bitlen,n.bits,n.cidr)

end Leanux.Proofs.WG.Config
