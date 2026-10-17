import Leanux.Env
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- The wheel's own earliest-due test is empty, with absence of a device allowed. -/
def NoTimerDue (j : UInt64) (s : Campaign2.Product.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → TimerWheel.nextDue d j = none


end Leanux.Proofs.WG.Progress
