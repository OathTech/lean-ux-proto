import Leanux.WG.Types

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Node owner plus the three fields read by allowed-IP serialization.
Parent links and child pointers are deliberately outside this observation. -/
def removalNodeView (n : AipNode) := (n.peer, n.bitlen, n.bits, n.cidr)

end Leanux.Proofs.WG.Config
