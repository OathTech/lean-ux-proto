import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.PeerScalarRetention
open Leanux Leanux.WG

abbrev Cell := Nat × Key × Nat × Option Endpoint
abbrev Map := PeerId → Option Cell
def cell (p : Peer) : Cell :=
  (p.internalId,p.presharedKey,p.persistentKeepaliveInterval,p.endpoint)
def peerValues (device : Option Device) : Map :=
  fun pid => (device.bind fun d=>d.peers[pid]?).map cell
def Retained (before after : Map) : Prop :=
  ∀ pid value, after pid=some value → before pid=some value
def observation (s : Campaign2.Snapshot) : Map := peerValues s.wg.device

end Leanux.Proofs.WG.Config.PeerScalarRetention
