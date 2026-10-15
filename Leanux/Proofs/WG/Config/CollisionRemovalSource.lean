import Leanux.Proofs.WG.Config.CollisionFrames
import Leanux.Proofs.WG.Config.LiveRemovalSource
import Leanux.Proofs.WG.Config.AllowedRemovalConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Normal completion supplies the actual clear effect; no static release
budget or independently postulated clear run is required. -/
theorem peerRemoveAfterDead_live_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerRemoveAfterDead pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ LiveRemovalEffect pid d p final) := by
  have hclear : Ensures (keypairsClear pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ cleared, w.k.wg = some cleared ∧
        ClearRun pid d [.next, .previous, .current] cleared ∧
        cleared.peers[pid]? = some (emptyKeysPeer p)) := by
    intro w u out pre run
    obtain ⟨cleared, device, steps⟩ := keypairsClear_effect pid d p resident w u out pre run
    have hp := keypairsClear_peer pid p w u out (by simp [peerAt, pre, resident]) run
    refine ⟨cleared, device, steps, ?_⟩
    simpa [peerAt, device, emptyKeysPeer] using hp
  rw [peerRemoveAfterDead_source]
  refine ensures_bind _ _ (removalDeadGuard_device pid d) (fun _ => ?_)
  refine ensures_bind _ _ hclear ?_
  intro u w result out pre run
  obtain ⟨cleared, device, steps, peer⟩ := pre
  have frame := clearRun_cleanupContext steps
  have hs : cleared.sendWorkQueue = [] := (congrArg Prod.fst frame).trans send
  have hc : cleared.clearWorkQueue = [] := (congrArg (fun x => x.2.1) frame).trans clear
  have hn : cleared.numPeers = d.numPeers := congrArg (fun x => x.2.2) frame
  have actual := removal_returns_ensures (removalAfterClear_returns pid cleared p peer live
    (by rwa [hn]) hs hc) w result out device run
  exact ⟨_, actual, cleared, steps, rfl⟩

/-- Derive the trie-removal relation from this original successful prefix,
then compose the actual quiet-queue suffix. This is not a totality theorem. -/
theorem peerRemove_live_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerRemove (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ CollisionRemovalEffect pid d p final) := by
  have body : Ensures (do peerMakeDead pid; peerRemoveAfterDead pid)
      (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ CollisionRemovalEffect pid d p final) := by
    refine ensures_bind _ _ (peerMakeDead_effect_pairs pid d p resident pairs) ?_
    intro u w result out pre run
    obtain ⟨removed, steps, device⟩ := pre
    have metadata := removalEffect_metadata steps
    have queues := removalEffect_queues steps
    have hcount : 0 < (deadPeerDevice removed pid p).numPeers := by
      have h := congrArg (fun x => x.2.2.2) metadata
      change removed.numPeers = d.numPeers at h
      change 0 < removed.numPeers
      rwa [h]
    have hs : (deadPeerDevice removed pid p).sendWorkQueue = [] :=
      (congrArg Prod.fst queues).trans send
    have hc : (deadPeerDevice removed pid p).clearWorkQueue = [] :=
      (congrArg Prod.snd queues).trans clear
    obtain ⟨final, actual, effect⟩ := peerRemoveAfterDead_live_effect pid
      (deadPeerDevice removed pid p) { erasePeerList p.allowedipsList p with isDead := true }
      (by simp [deadPeerDevice, withPeer])
      (by simpa only [erasePeerList_refcount] using live) hcount hs hc w result out device run
    exact ⟨final, actual, removed, steps, effect⟩
  unfold peerRemove
  have guard : Ensures (branch .peerRemoveNull (some pid).isNone)
      (fun w => w.k.wg = some d) (fun result w => result = false ∧ w.k.wg = some d) := by
    rw [ensures_iff]
    mvcgen [branch]
  refine ensures_bind _ _ guard ?_
  intro result w ret out pre run
  obtain ⟨rfl, device⟩ := pre
  exact body w ret out device run

end Leanux.Proofs.WG.Config
