import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.Env

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Precisely the send-worker loop's normal completion alternatives. Other
work, timer flags, ring contents and pending-worker bookkeeping are unrestricted. -/
def SendWorkersComplete (s : Campaign2.Product.Snapshot) : Prop :=
  s.wg.device = none ∨ ∃ d, s.wg.device = some d ∧ d.sendWorkQueue = []

end Leanux.Proofs.WG.Progress
