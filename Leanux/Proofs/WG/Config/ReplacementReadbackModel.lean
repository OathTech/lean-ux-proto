import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.AllowedRemovalModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- Pure getter inputs after empty replacement. Roots and node records here
are not an execution state: the actual removal successor remains explicit. -/
def replacementReadbackInputs (d : Device) (ids : List NodeId) : Device :=
  {requestGeneration d with
    peers := d.peers.map (fun _ p => erasePeerList ids p)
    peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + (if ids.isEmpty then 0 else 1)}}

/-- Fields outside the peer/node stores and allowed-IP table. -/
def replacementOuter (d : Device) : Device :=
  {d with peers := {}, nodes := {}, peerAllowedips := {}}

end Leanux.Proofs.WG.Config
