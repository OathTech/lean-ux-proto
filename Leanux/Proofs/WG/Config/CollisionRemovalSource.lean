import Leanux.Proofs.WG.Config.CollisionFrames
import Leanux.Proofs.WG.Config.LiveRemovalSource
import Leanux.Proofs.WG.Config.AllowedRemovalConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Normal completion supplies the actual clear effect; no static release
budget or independently postulated clear run is required. -/
theorem peerRemoveAfterDead_live_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerRemoveAfterDead pid) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ LiveRemovalEffect pid d p final) := by
  have hclear : Ensures (keypairsClear pid) (fun w => w.dev = some d)
      (fun _ w => ∃ cleared, w.dev = some cleared ∧
        ClearRun pid d [.next, .previous, .current] cleared ∧
        cleared.peers[pid]? = some (emptyKeysPeer p)) := by
    intro w ambient u out after pre run
    obtain ⟨cleared, device, steps⟩ := keypairsClear_effect pid d p resident w ambient u out after pre run
    have hp := keypairsClear_peer pid p w ambient u out after (by simp [peerAt, pre, resident]) run
    refine ⟨cleared, device, steps, ?_⟩
    simpa [peerAt, device, emptyKeysPeer] using hp
  rw [peerRemoveAfterDead_source]
  refine ensures_bind _ _ (removalDeadGuard_device pid d) (fun _ => ?_)
  refine ensures_bind _ _ hclear ?_
  intro u g ambient result final after pre run
  obtain ⟨cleared, device, steps, peer⟩ := pre
  have frame := clearRun_cleanupContext steps
  have hs : cleared.sendWorkQueue = [] := (congrArg Prod.fst frame).trans send
  have hc : cleared.clearWorkQueue = [] := (congrArg (fun x => x.2.1) frame).trans clear
  have hn : cleared.numPeers = d.numPeers := congrArg (fun x => x.2.2) frame
  obtain ⟨value, timedState, timerAmbient, timerRun, timedDevice⟩ :=
    timersStop_quiet_returns pid cleared (emptyKeysPeer p) peer hc g ambient device
  cases value
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), remaining) =>
          ((next value).run middle).run remaining) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  simp only [bindRun, timerRun, okBind] at run
  simp [getDev, timedDevice] at run
  split at run
  · simp [unsupported, AmbientM.unsupported] at run; cases run
  · have actual := removalAfterClear_returns pid cleared p peer live (by rwa [hn]) hs hc
      g ambient device
    have normal : ((do
        timersStop pid
        drainHandshakeSendWq none
        decrementPeerCount
        peerPut (some pid) : WG.M Unit).run g).run ambient =
        .ok ((result, final), after) := by
      simpa only [bindRun, timerRun, okBind] using run
    rw [normal] at actual
    cases refusal : Index.peerReleaseRefusal pid (quietCleanupPeer p)
    · rw [refusal] at actual
      obtain ⟨observed, returned, post⟩ := actual
      simp only [Campaign2.observeResult, Except.map, Except.ok.injEq, Prod.mk.injEq] at returned
      obtain ⟨_, rfl⟩ := returned
      exact ⟨_, post, cleared, steps, rfl⟩
    · rw [refusal] at actual
      cases actual

/-- Derive trie removal from the successful original prefix and compose its
actual suffix. The contract asserts normal-return effects, not totality. -/
theorem peerRemove_live_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerRemove (some pid)) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ CollisionRemovalEffect pid d p final) := by
  have body : Ensures (do peerMakeDead pid; peerRemoveAfterDead pid)
      (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ CollisionRemovalEffect pid d p final) := by
    refine ensures_bind _ _ (peerMakeDead_effect_pairs pid d p resident pairs) ?_
    intro u w ambient result out after pre run
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
      (by simpa only [erasePeerList_refcount] using live) hcount hs hc w ambient result out after device run
    exact ⟨final, actual, removed, steps, effect⟩
  unfold peerRemove
  have guard : Ensures (branch .peerRemoveNull (some pid).isNone : WG.M Bool)
      (fun w => w.dev = some d) (fun result w => result = false ∧ w.dev = some d) := by
    intro g ambient value final after pre run
    change Except.ok ((false, g), _) = Except.ok ((value, final), after) at run
    cases run
    exact ⟨rfl, pre⟩
  refine ensures_bind _ _ guard ?_
  intro result w ambient ret out after pre run
  obtain ⟨rfl, device⟩ := pre
  exact body w ambient ret out after device run

end Leanux.Proofs.WG.Config
