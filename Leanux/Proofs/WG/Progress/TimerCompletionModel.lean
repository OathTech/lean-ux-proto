import Leanux.Env
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- The exact final queue tests made by a fired timer episode. Ring emptiness
is the ring's own `empty` operation, not a claim about physical occupancy. -/
def TimerCompletionGuard (s : Campaign2.Product.Snapshot) : Prop :=
  ∃ d, s.wg.device = some d ∧
    d.sendWorkQueue.isEmpty = true ∧ d.clearWorkQueue.isEmpty = true ∧
    d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true


end Leanux.Proofs.WG.Progress
