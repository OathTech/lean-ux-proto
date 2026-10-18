import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.Runner

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedInitialized
open Lean Leanux

/-- The runner outcome projected to WireGuard and its fixture; an error retains
its original syscall index and Stop, with no final snapshot. -/
abbrev Inspection := Except (Nat × Stop) (Json × Campaign2.Product.Snapshot)

end Leanux.Proofs.WG.Index.ReachedInitialized
