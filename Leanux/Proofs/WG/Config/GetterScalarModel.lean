import Leanux.Proofs.WG.Config.PeerScalarRetentionModel
import Leanux.Proofs.WG.TimerDiscipline.SendView
import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG
abbrev Cell := Nat × Key × Nat × Option Endpoint

abbrev Map := PeerId → Option Cell

def cell (p : Peer) : Cell :=
  (p.internalId,p.presharedKey,p.persistentKeepaliveInterval,
    p.endpoint.map TimerDiscipline.socketEndpoint)

def values (device : Option Device) : Map :=
  fun pid => (device.bind fun d => d.peers[pid]?).map GetterScalar.cell

def observation (s : Campaign2.Snapshot) : Map := values s.wg.device

def Keeps (entry final : Campaign2.Snapshot) : Prop :=
  ∀ pid c, observation final pid=some c → observation entry pid=some c

def fromFull (c : PeerScalarRetention.Cell) : Cell :=
  (c.1,c.2.1,c.2.2.1,c.2.2.2.map TimerDiscipline.socketEndpoint)


end Leanux.Proofs.WG.Config.GetterScalar
