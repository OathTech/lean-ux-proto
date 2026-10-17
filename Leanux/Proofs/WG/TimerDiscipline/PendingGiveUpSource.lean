import Leanux.Proofs.WG.TimerDiscipline.PendingGiveUpModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- This branch performs no hidden read and returns for every original realization.
The current exact effect includes removal of the keepalive wheel entry. -/
theorem pendingGiveUp_run (pid : PeerId) (d : Device) (p : Peer) (expiry : UInt64)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry)
    (entry : World) (device : entry.wg.dev = some d) :
    (liftWG (expiredRetransmitHandshake pid)).run entry = .ok ((),
      { entry with
        wg := { entry.wg with dev := some (giveUpWheelDevice d pid p) }
        ambient := {entry.ambient with steps := pendingGiveUpSteps p entry.ambient.netRxSection entry.ambient.steps} }) := by
  change ((((expiredRetransmitHandshake pid).run entry.wg).run entry.ambient) >>= fun ((value, current), inputs) =>
    .ok (value, {entry with wg := current, ambient := inputs})) = _
  simp [expiredRetransmitHandshake, getPeer, getDev, setPeer, modifyDev,
    branchCmp, branch, AmbientM.branchCmp, AmbientM.branch, delTimer, purgeStagedPackets,
    device, resident, limit, pending, Peer.setTimer, Peer.setWheel, Peer.timerPending, Peer.timer,
    giveUpWheelDevice, giveUpWheelPeer, pendingGiveUpSteps]

/-- Total full-Product contract with the original resident, give-up and pending
zero-key premises. The wheel correction does not require timer consistency. -/
theorem pendingGiveUp_returns (pid : PeerId) (d : Device) (p : Peer) (expiry : UInt64)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Returns (liftWG (expiredRetransmitHandshake pid))
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => final = pendingGiveUpView entry d pid p) := by
  intro actual pre
  refine ⟨(), _, pendingGiveUp_run pid d p expiry resident limit pending actual pre.2, ?_⟩
  rcases pre with ⟨rfl, _⟩
  rfl

end Leanux.Proofs.WG.TimerDiscipline
