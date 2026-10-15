import Leanux.Proofs.WG.Campaign2.View
import Leanux.Proofs.WG.Config.Model
import Leanux.WG.Socket

/-! State-only predicates for the configuration claims. These definitions inspect
only the explicit WireGuard projection, never an enclosing subsystem store. -/
namespace Leanux.Proofs.WG.Config.ClaimView
open Leanux Leanux.WG Campaign2

def portState (k : Core) : Option (Nat × Option Nat × Option Nat × Bool) :=
  k.device.map fun d => (d.incomingPort, d.sock4, d.sock6, d.running)

def sourcesClear (k : Core) (pids : List PeerId) : Prop :=
  ∀ pid ∈ pids, ∃ p, (k.device.bind fun d => d.peers[pid]?) = some p ∧ sourceClear p

def clearedPeers (initial : Device) (k : Core) (seen : List PeerId) : Prop :=
  ∀ q, if q ∈ seen then
    ∃ p reset, initial.peers[q]? = some p ∧
      (k.device.bind fun d => d.peers[q]?) = some (clearedSource p reset)
  else (k.device.bind fun d => d.peers[q]?) = initial.peers[q]?

def zeroPortEffects (d : Device) (w : Snapshot) : Prop :=
  if d.incomingPort = 0 then w.wg.device = some d
  else clearedPeers d w.wg.toCore d.peerList ∧
    if d.running then ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      w.wg.device.map withoutPeers = some (withoutPeers
        { d with sock4 := some port, sock6 := some port, incomingPort := port })
    else w.wg.device.map withoutPeers = some (withoutPeers { d with incomingPort := 0 })

def selectsDevice (w : Snapshot) (d : Device) : Prop :=
  (w.wg.fixtureNetDevices ++ [(d.ifname, d.ifindex, some "wireguard")]).find?
    (fun r => some r.2.1 == some d.ifindex) =
      some (d.ifname, d.ifindex, some "wireguard")

end Leanux.Proofs.WG.Config.ClaimView
