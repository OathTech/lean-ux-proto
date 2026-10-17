import Leanux.Proofs.WG.Config.MultiPeerDumpModel
import Leanux.Proofs.WG.Config.MultiPeerCoalesceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual ordered fixed peer attributes, including endpoint serialization,
with the coalescer's empty allowed_ips normalization for every list occurrence. -/
def multiPeerJson (d : Device) (peers : PeerId → Peer) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
    (((multiPeerParts peers d.peerList).map peerDumpWithIps).toArray.map
      (fun p => Json.mkObj p.attrs)))])


end Leanux.Proofs.WG.Config
