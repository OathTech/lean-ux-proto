import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Queues.CurrentSlots

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace View
def StagedIndexReady (s : Campaign2.Snapshot) : Prop :=
  ∀d, s.wg.device = some d → CurrentSlots.SlotInv (Affiliation.state d) ∧ DeviceIndexCore d
end View

end Leanux.Proofs.WG.Index
