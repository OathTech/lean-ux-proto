import Leanux.Proofs.WG.Peers.ConfiguredIdentity
import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The existing configured-state invariant, expressed only on the campaign
projection. Its resident bounds imply vacancy at the actual next-peer cursor. -/
def View.ConfiguredSafe (s : Campaign2.Snapshot) : Prop :=
  ∀ state, s.wg.device.map ConfiguredIdentity.state = some state →
    ConfiguredIdentity.State.Inv state
end Leanux.Proofs.WG.Index
