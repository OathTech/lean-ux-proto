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
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect d p.allowedipsList removed ∧
        w.k.wg = some (withPeer removed pid
          { erasePeerList p.allowedipsList p with refcount := p.refcount - 1 })) := by
  have body : Ensures (do
      removeByPeer pid
      peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid)
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect d p.allowedipsList removed ∧
        w.k.wg = some (withPeer removed pid
          { erasePeerList p.allowedipsList p with refcount := p.refcount - 1 })) := by
    refine ensures_bind _ _ (removeByPeer_effect_pairs pid d p resident pairs) ?_
    intro u w ret out pre run
    obtain ⟨removed, device, steps⟩ := pre
    let q := erasePeerList p.allowedipsList p
    have peer : removed.peers[pid]? = some q := by
      simpa [resident, q] using removalEffect_peers steps pid
    have refs : q.refcount = p.refcount := erasePeerList_refcount _ _
    have effect := removal_returns_ensures
      (replacementTail_down key pid removed q peer (by rwa [refs])
        ((removalEffect_running steps).trans down)) w ret out device run
    exact ⟨effect.1, removed, steps, by simpa only [q, refs] using effect.2⟩
  simp only [peerConfigUpdateSource, replaceAllowedipsAttrs,
    WGPEER_F_REPLACE_ALLOWEDIPS, WGPEER_F_REMOVE_ME]
  have guards : Ensures (do
      _ ← branch .peerRemoveMe false
      _ ← branch .peerSetPsk false
      _ ← branch .peerHasEndpoint false
      _ ← branch .peerReplaceAips true
      pure ()) (fun w => w.k.wg = some d) (fun _ w => w.k.wg = some d) := by
    rw [ensures_iff]
    mvcgen [branch]
  have composed := ensures_bind _ _ guards (fun _ => body)
  have disjoint : (2 : UInt32) &&& 1 = 0 := by decide
  simpa [branch, bind_assoc, pure_bind, bind_pure_comp, replaceAllowedipsAttrs,
    WGPEER_F_REPLACE_ALLOWEDIPS, disjoint] using composed

theorem setPeer_replace_effect_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 }) p.allowedipsList removed ∧
        w.k.wg = some (generalReplacementDevice removed pid p)) := by
  let acquired := { p with refcount := p.refcount + 1 }
  let acquiredDevice := withPeer d pid acquired
  have hl := (ensures_iff _ _ _).mp (removal_returns_ensures
    ((returns_iff _ _ _).mpr (pubkeyLookup_present_returns key pid d p found resident live bounded)))
  have hu := (ensures_iff _ _ _).mp
    (replacementUpdate_effect_pairs key pid acquiredDevice acquired
      (by simp [acquiredDevice, withPeer]) pairs (by simpa [acquired] using live) down)
  rw [← setPeerCmd_source, ensures_iff]
  simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS]
  mvcgen [WG.andM, branch, invariant, hl, hu]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [generalReplacementDevice, acquiredDevice, acquired]
  all_goals subst_vars
  all_goals first | exact hu _ (by simp_all [acquiredDevice, acquired]) | grind only

end Leanux.Proofs.WG.Config
