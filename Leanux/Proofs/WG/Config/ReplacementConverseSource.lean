import Leanux.Proofs.WG.Config.AllowedGeneralReplacement
import Leanux.Proofs.WG.Config.AllowedRemovalConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Recover the removal relation from the actual original prefix, then execute
the unchanged tail from its resulting device. No supplied run witness. -/
theorem replacementUpdate_effect_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (retained : 1 < p.refcount) (down : d.running = false) :
    Ensures (peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect d p.allowedipsList removed ∧
        w.dev = some (withPeer removed pid
          { erasePeerList p.allowedipsList p with refcount := p.refcount - 1 })) := by
  have body : Ensures (do
      removeByPeer pid
      peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid)
      (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect d p.allowedipsList removed ∧
        w.dev = some (withPeer removed pid
          { erasePeerList p.allowedipsList p with refcount := p.refcount - 1 })) := by
    refine ensures_bind _ _ (removeByPeer_effect_pairs pid d p resident pairs) ?_
    intro u w ambient ret out after pre run
    obtain ⟨removed, device, steps⟩ := pre
    let q := erasePeerList p.allowedipsList p
    have peer : removed.peers[pid]? = some q := by
      simpa [resident, q] using removalEffect_peers steps pid
    have refs : q.refcount = p.refcount := erasePeerList_refcount _ _
    have effect := removal_returns_ensures_native
      (replacementTail_down key pid removed q peer (by rwa [refs])
        ((removalEffect_running steps).trans down)) w ambient ret out after device run
    exact ⟨effect.1, removed, steps, by simpa only [q, refs] using effect.2⟩
  intro g ambient result final after device run
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .peerRemoveMe false)
    .peerSetPsk false) .peerHasEndpoint false) .peerReplaceAips true
  have source : ((peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid).run g).run ambient =
      (((do removeByPeer pid
            peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid) : WG.M Int).run g).run before := by
    have removeOff : (2 : UInt32) &&& 1 = 0 := by decide
    simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS,
      WGPEER_F_REMOVE_ME, branch, AmbientM.branch, removeOff, before, mark]
  exact body g before result final after device (source.symm.trans run)

theorem setPeer_replace_effect_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 }) p.allowedipsList removed ∧
        w.dev = some (generalReplacementDevice removed pid p)) := by
  intro g ambient result final after device run
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark ambient
    .peerHasPubkey true) .peerPubkeyLen true) .peerHasPsk false)
    .peerHasFlags true) .peerBadFlags false) .peerHasProtocol false
  let acquired := {p with refcount := p.refcount + 1}
  let acquiredDevice := withPeer d pid acquired
  obtain ⟨got, middle, a1, lookupRun, value, acquiredState⟩ :=
    (returns_iff _ _ _).mpr (pubkeyLookup_present_returns key pid d p found resident live bounded)
      g before device
  subst got
  have source : ((setPeerCmd (replaceAllowedipsAttrs key)).run g).run ambient =
      ((peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
        WGPEER_F_REPLACE_ALLOWEDIPS none pid).run middle).run (mark a1 .peerNotFound false) := by
    have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
    rw [← setPeerCmd_source]
    simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS,
      WG.andM, branch, AmbientM.branch, good]
    rw [show ((pubkeyLookup key).run g).run before = .ok ((some pid, middle), a1) from lookupRun]
    rfl
  obtain ⟨value, removed, steps, changed⟩ :=
    replacementUpdate_effect_pairs key pid acquiredDevice acquired
      (by simp [acquiredDevice, withPeer]) pairs (by simpa [acquired] using live) down
      middle (mark a1 .peerNotFound false) result final after acquiredState (source.symm.trans run)
  refine ⟨value, removed, steps, ?_⟩
  simpa [generalReplacementDevice, acquired] using changed

end Leanux.Proofs.WG.Config
