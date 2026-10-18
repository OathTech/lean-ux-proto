import Leanux.Proofs.WG.Noise.DriverTagConsumeFrames
import Leanux.Proofs.WG.Noise.DriverTagSilentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Silent
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem consumeDataDone_preserves (entry : TagMap) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (consumeDataDone pid pkt endpoint)) :=
  lift_preserves entry _ (fun initial => consumeDataDone_retained initial pid pkt endpoint)

end Leanux.Proofs.WG.Noise.DriverTags.Silent
