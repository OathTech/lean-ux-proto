import Leanux.Proofs.WG.Config.LiveRemovalFrames
import Leanux.Proofs.WG.Config.QuietRemoval
import Leanux.Proofs.WG.Noise.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The suffix begins at the actual post-clear device, without repeating slot writes. -/
theorem removalAfterClear_returns (pid : PeerId) (cleared : Device) (p : Peer)
    (resident : cleared.peers[pid]? = some (emptyKeysPeer p))
    (live : 0 < p.refcount) (count : 0 < cleared.numPeers)
    (send : cleared.sendWorkQueue = []) (clear : cleared.clearWorkQueue = []) :
    Returns (do
      timersStop pid
      drainHandshakeSendWq none
      decrementPeerCount
      peerPut (some pid)) (fun w => w.k.wg = some cleared)
      (fun _ w => w.k.wg = some (removedAfterClear cleared pid p)) := by
  let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
  have frame := deleteTimers_withoutPeers PeerTimer.all cleared pid (emptyKeysPeer p)
  have hs : timed.sendWorkQueue = [] := (congrArg Device.sendWorkQueue frame).trans send
  have hc : timed.clearWorkQueue = [] := (congrArg Device.clearWorkQueue frame).trans clear
  have hn : timed.numPeers = cleared.numPeers := by
    simpa only [withoutPeers] using congrArg Device.numPeers frame
  have hpeer : timed.peers[pid]? = some (quietCleanupPeer p) :=
    deleteTimers_resident _ _ _ _ resident
  have hlive : 0 < (quietCleanupPeer p).refcount := by
    rw [quietCleanup_refcount]; exact live
  have hd : Returns (drainHandshakeSendWq none) (fun w => w.k.wg = some timed)
      (fun _ w => w.k.wg = some timed) := by
    intro w pre
    exact ⟨(), w, drain_empty _ _ w pre hs hc, pre⟩
  refine returns_bind _ _ (timersStop_quiet_returns pid cleared (emptyKeysPeer p) resident clear) (fun _ => ?_)
  refine returns_bind _ _ hd (fun _ => ?_)
  refine returns_bind _ _ (decrementPeerCount_returns timed (by rwa [hn])) (fun _ => ?_)
  exact Index.peerPut_exact pid { timed with numPeers := timed.numPeers - 1 }
    (quietCleanupPeer p) hpeer hlive

theorem peerRemoveAfterDead_live_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Returns (peerRemoveAfterDead pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ LiveRemovalEffect pid d p final) := by
  have hg : Returns (removalDeadGuard pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [removalDeadGuard, getPeer, getDev, getK, branch, invariant, unsupported]
    all_goals simp_all
  have hclear : Returns (keypairsClear pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ cleared, w.k.wg = some cleared ∧
        ClearRun pid d [.next, .previous, .current] cleared ∧
        cleared.peers[pid]? = some (emptyKeysPeer p)) := by
    intro w pre
    obtain ⟨u, after, run, cleared, device, steps⟩ :=
      keypairsClear_returns_ready pid d p resident ready w pre
    have hp := keypairsClear_peer pid p w u after (by simp [peerAt, pre, resident]) run
    refine ⟨u, after, run, cleared, device, steps, ?_⟩
    simpa [peerAt, device, emptyKeysPeer] using hp
  rw [peerRemoveAfterDead_source]
  refine returns_bind _ _ hg (fun _ => ?_)
  refine returns_bind _ _ hclear ?_
  intro u w pre
  obtain ⟨cleared, device, steps, peer⟩ := pre
  have frame := clearRun_cleanupContext steps
  have hs : cleared.sendWorkQueue = [] := (congrArg Prod.fst frame).trans send
  have hc : cleared.clearWorkQueue = [] := (congrArg (fun x => x.2.1) frame).trans clear
  have hn : cleared.numPeers = d.numPeers := congrArg (fun x => x.2.2) frame
  obtain ⟨v, final, run, post⟩ := removalAfterClear_returns pid cleared p peer live
    (by rwa [hn]) hs hc w device
  exact ⟨v, final, run, _, post, cleared, steps, rfl⟩

theorem peerRemove_live_returns (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Returns (peerRemove (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        LiveRemovalEffect pid (deadPeerDevice removed pid p)
          { erasePeerList p.allowedipsList p with isDead := true } final) := by
  have metadata := removalEffect_metadata steps
  have queues := removalEffect_queues steps
  have keys := removalEffect_keypairs steps
  have hp := erasePeerList_exceptList p.allowedipsList p
  have hkeys : clearKeys { erasePeerList p.allowedipsList p with isDead := true } = clearKeys p := by
    simpa only [clearKeys] using congrArg clearKeys hp
  have hready : ClearReady (deadPeerDevice removed pid p)
      (clearKeys { erasePeerList p.allowedipsList p with isDead := true }) := by
    rw [hkeys]
    intro id used
    obtain ⟨k, found, word, budget⟩ := ready id used
    refine ⟨k, ?_, word, budget⟩
    change removed.keypairs[id]? = some k
    rw [keys]
    exact found
  have hcount : 0 < (deadPeerDevice removed pid p).numPeers := by
    have h := congrArg (fun x => x.2.2.2) metadata
    change removed.numPeers = d.numPeers at h
    change 0 < removed.numPeers
    rwa [h]
  have hs : (deadPeerDevice removed pid p).sendWorkQueue = [] :=
    (congrArg Prod.fst queues).trans send
  have hc : (deadPeerDevice removed pid p).clearWorkQueue = [] :=
    (congrArg Prod.snd queues).trans clear
  have after := peerRemoveAfterDead_live_returns pid (deadPeerDevice removed pid p)
    { erasePeerList p.allowedipsList p with isDead := true }
    (by simp [deadPeerDevice, withPeer]) rfl
    (by simpa only [erasePeerList_refcount] using live) hcount hready hs hc
  have body := returns_bind _ _ (peerMakeDead_returns pid p d removed resident steps) (fun _ => after)
  unfold peerRemove
  have guard : Returns (branch .peerRemoveNull (some pid).isNone)
      (fun w => w.k.wg = some d) (fun result w => result = false ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [branch]
  refine returns_bind _ _ guard ?_
  intro result w pre
  obtain ⟨rfl, device⟩ := pre
  exact body w device

end Leanux.Proofs.WG.Config
