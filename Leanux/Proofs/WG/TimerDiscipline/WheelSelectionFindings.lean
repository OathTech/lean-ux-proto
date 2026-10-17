import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Kernel.TimerWheel

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Logical-expiry readiness from the historical dispatcher is insufficient
for the actual wheel selector on arbitrary states. No reachable-state or
complete-callback claim is made: this isolates the missing representation fact. -/
theorem logical_expiry_without_wheel_selection :
    ∃ (d : Device) (p : Peer),
      d.peers[0]? = some p ∧ d.peerList = [0] ∧
      p.timerRetransmitHandshake = some 1 ∧
      duePeers d .retransmitHandshake 2 = [0] ∧
      p.wheel .retransmitHandshake = none ∧ TimerWheel.nextDue d 2 = none := by
  let p : Peer := {
    remoteStatic := [], presharedKey := [], precomputedStaticStatic := []
    internalId := 0, timerRetransmitHandshake := some 1 }
  let d : Device := {
    ifindex := 0, ifname := "wg0", peerList := [0]
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 p }
  refine ⟨d, p, ?_, rfl, rfl, ?_, rfl, ?_⟩
  · simp [d]
  · simp [duePeers, d, p, Peer.timer, timeBefore, timeAfter]
  · simp [TimerWheel.nextDue, TimerWheel.due, d, p, PeerTimer.all, Peer.wheel]

end Leanux.Proofs.WG.TimerDiscipline
