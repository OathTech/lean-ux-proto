import Leanux.Proofs.WG.Config.QuietRemovalSource
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem quietCleanup_resident (d : Device) (pid : PeerId) (p : Peer) :
    (quietCleanupDevice d pid p).peers[pid]? = some (quietCleanupPeer p) :=
  deleteTimers_resident _ _ _ _ (by simp [emptyKeysDevice, withPeer])

theorem decrementPeerCount_returns (d : Device) (positive : 0 < d.numPeers) :
    Returns decrementPeerCount (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with numPeers := d.numPeers - 1 }) := by
  rw [returns_iff]
  mvcgen [decrementPeerCount, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals omega

theorem peerRemoveAfterDead_quiet_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true) (live : 0 < p.refcount)
    (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Returns (peerRemoveAfterDead pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (quietRemovedDevice d pid p)) := by
  have hg : Returns (removalDeadGuard pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [removalDeadGuard, getPeer, getDev, getK, branch, invariant, unsupported]
    all_goals simp_all
  have hf := quietCleanup_frame d pid p
  have hs := congrArg Device.sendWorkQueue hf
  have hc := congrArg Device.clearWorkQueue hf
  have hn := congrArg Device.numPeers hf
  simp only [withoutPeers] at hs hc hn
  rw [send] at hs
  rw [clear] at hc
  have positive : 0 < (quietCleanupDevice d pid p).numPeers := by rw [hn]; exact count
  have hd : Returns (drainHandshakeSendWq none)
      (fun w => w.k.wg = some (quietCleanupDevice d pid p))
      (fun _ w => w.k.wg = some (quietCleanupDevice d pid p)) := by
    intro w pre
    exact ⟨(), w, drain_empty _ _ w pre hs hc, pre⟩
  rw [peerRemoveAfterDead_source]
  refine returns_bind _ _ hg (fun _ => ?_)
  refine returns_bind _ _ (keypairsClear_empty_returns pid d p resident empty) (fun _ => ?_)
  refine returns_bind _ _ (timersStop_quiet_returns pid (emptyKeysDevice d pid p) (emptyKeysPeer p)
    (by simp [emptyKeysDevice, withPeer]) clear) (fun _ => ?_)
  refine returns_bind _ _ hd (fun _ => ?_)
  refine returns_bind _ _ (decrementPeerCount_returns (quietCleanupDevice d pid p) positive) (fun _ => ?_)
  exact Index.peerPut_exact pid
    { quietCleanupDevice d pid p with numPeers := (quietCleanupDevice d pid p).numPeers - 1 }
    (quietCleanupPeer p) (quietCleanup_resident d pid p)
    (by simpa only [quietCleanup_refcount] using live)

theorem peerRemove_quiet_returns (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Returns (peerRemove (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (quietRemovedDevice (deadPeerDevice removed pid p) pid
        { erasePeerList p.allowedipsList p with isDead := true })) := by
  have metadata := removalEffect_metadata steps
  have queues := removalEffect_queues steps
  have hp := erasePeerList_exceptList p.allowedipsList p
  have slots : (erasePeerList p.allowedipsList p).keypairNext = none ∧
      (erasePeerList p.allowedipsList p).keypairPrevious = none ∧
      (erasePeerList p.allowedipsList p).keypairCurrent = none := by
    have hn := congrArg Peer.keypairNext hp
    have hv := congrArg Peer.keypairPrevious hp
    have hc := congrArg Peer.keypairCurrent hp
    exact ⟨hn.trans empty.1, hv.trans empty.2.1, hc.trans empty.2.2⟩
  have hcount : 0 < (deadPeerDevice removed pid p).numPeers := by
    have h := congrArg (fun x => x.2.2.2) metadata
    change removed.numPeers = d.numPeers at h
    change 0 < removed.numPeers
    rwa [h]
  have hs : (deadPeerDevice removed pid p).sendWorkQueue = [] :=
    (congrArg Prod.fst queues).trans send
  have hc : (deadPeerDevice removed pid p).clearWorkQueue = [] :=
    (congrArg Prod.snd queues).trans clear
  have after := peerRemoveAfterDead_quiet_returns pid (deadPeerDevice removed pid p)
    { erasePeerList p.allowedipsList p with isDead := true }
    (by simp [deadPeerDevice, withPeer]) rfl
    (by simpa only [erasePeerList_refcount] using live) hcount slots hs hc
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
