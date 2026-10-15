import Leanux.Proofs.WG.TimerDiscipline.PendingGiveUpModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- This original branch has no hidden read and returns for every realization. -/
theorem pendingGiveUp_run (pid : PeerId) (d : Device) (p : Peer) (expiry : UInt64)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry)
    (entry : World) (device : entry.k.wg = some d) :
    (expiredRetransmitHandshake pid).run entry = .ok ((),
      { entry with
        k := { entry.k with wg := some (giveUpDevice d pid p) }
        steps := pendingGiveUpSteps p entry.netRxSection entry.steps }) := by
  simp [expiredRetransmitHandshake, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, branchCmp, branch, delTimer, purgeStagedPackets, device, resident,
    limit, pending, Peer.setTimer, Peer.timerPending, Peer.timer,
    giveUpDevice, giveUpPeer, pendingGiveUpSteps, StateT.run_bind, StateT.run_pure]
  rfl

theorem pendingGiveUp_returns (pid : PeerId) (d : Device) (p : Peer) (expiry : UInt64)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry) (entry : Snapshot) :
    Campaign2.Returns (expiredRetransmitHandshake pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => final = pendingGiveUpView entry d pid p) := by
  intro actual pre
  refine ⟨(), _, pendingGiveUp_run pid d p expiry resident limit pending actual pre.2, ?_⟩
  rcases pre with ⟨rfl, _⟩
  rfl

end Leanux.Proofs.WG.TimerDiscipline
