import Leanux.Proofs.WG.Noise.DriverTagModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Peers.Allocation

/-! Physical projection facts for the driver tag observer. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Lifetimes

theorem peerStampStore_snapshot (g : WGWorld) (ambient : Ambient) :
    peerStampStore (Campaign2.snapshot g ambient) = Peers.snapshot g := rfl

end Leanux.Proofs.WG.Noise.DriverTags
