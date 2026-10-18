import Leanux.Proofs.WG.Index.LifecycleModel
import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.RetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Ordinary driver-boundary index facts. Nonempty retirement lists remain
local to removal proofs; this predicate contains no reachability assertion. -/
def DeviceIndexCore (d : Device) : Prop :=
  DeviceTablesSafe d ∧ HashSlotCoverage d ∧ HashedOwnersCoherent d ∧
    DeadHashedReserved [] d

namespace View
def IndexCore (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → DeviceIndexCore d
end View
end Leanux.Proofs.WG.Index
