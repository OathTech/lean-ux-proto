import Leanux.Proofs.WG.Index.ReachedIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace View
/-- Combined index facts and the actual selected resident's extra reference.
This is a projected local cut, not an initialized history assertion. -/
def IndexCoreHeld (pid : PeerId) (s : Campaign2.Snapshot) : Prop :=
  IndexCore s ∧ ∃ d p, s.wg.device=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount
end View
end Leanux.Proofs.WG.Index
