import Leanux.Proofs.WG.Config.AllowedReplacement
import Leanux.Proofs.WG.Config.AllowedRemovalEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem replacementUpdate_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount) (down : d.running = false)
    (steps : RemovalEffect d p.allowedipsList removed) :
    Returns (peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (withPeer removed pid { (erasePeerList p.allowedipsList p) with refcount := p.refcount - 1 })) := by
  let q := erasePeerList p.allowedipsList p
  have peer : removed.peers[pid]? = some q := by
    simpa [resident, q] using removalEffect_peers steps pid
  have count : q.refcount = p.refcount := erasePeerList_refcount _ _
  have running : removed.running = false := (removalEffect_running steps).trans down
  have hr := (returns_iff _ _ _).mp (removeByPeer_general pid p d removed resident steps)
  have ht := (returns_iff _ _ _).mp
    (replacementTail_down key pid removed q peer (by simpa [count] using retained) running)
  rw [returns_iff]
  simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS, WGPEER_F_REMOVE_ME]
  mvcgen [branch, hr, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [q, erasePeerList_refcount]
  all_goals exact ht _ (by assumption)

def generalReplacementDevice (removed : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer removed pid
    { (erasePeerList p.allowedipsList { p with refcount := p.refcount + 1 }) with refcount := p.refcount }

theorem setPeer_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Returns (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (generalReplacementDevice removed pid p)) := by
  have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
  let acquired := { p with refcount := p.refcount + 1 }
  let acquiredDevice := withPeer d pid acquired
  have hl := pubkeyLookup_present_returns key pid d p found peer live bounded
  have hu := (returns_iff _ _ _).mp
    (replacementUpdate_general key pid acquiredDevice removed acquired
      (by simp [acquiredDevice, withPeer]) (by simpa [acquired] using live) down steps)
  rw [← setPeerCmd_source, returns_iff]
  simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS]
  mvcgen [WG.andM, branch, invariant, hl, hu]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [generalReplacementDevice, acquiredDevice, acquired]
  all_goals subst_vars
  all_goals first | exact hu _ (by simp_all) | grind only

theorem devicePeers_replace_general (selector : Device) (key : Key) (pid : PeerId)
    (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ devicePeersSource (replaceAllowedipsDeviceAttrs selector key)
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.k.wg = some (generalReplacementDevice removed pid p)⌝⦄ := by
  have hp := (returns_iff _ _ _).mp
    (setPeer_replace_general key pid d removed p found peer live bounded down steps)
  simp [devicePeersSource, replaceAllowedipsDeviceAttrs, List.forIn_cons, List.forIn_nil]
  mvcgen [branch, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem setDevice_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect
      (withPeer { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (generalReplacementDevice removed pid p)) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hp := devicePeers_replace_general d key pid updated removed p found peer live bounded down steps
  rw [← wgSetDevice_source, returns_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, replaceAllowedipsDeviceAttrs]
  mvcgen [WG.orM, WG.andM, branch, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals first | exact hp _ (by simp_all [updated]) | grind only

theorem generalReplacement_peer (removed : Device) (pid : PeerId) (p : Peer) :
    ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
      q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId := by
  refine ⟨{ (erasePeerList p.allowedipsList { p with refcount := p.refcount + 1 }) with
    refcount := p.refcount }, by simp [generalReplacementDevice, withPeer], ?_, rfl, ?_⟩
  · exact erasePeerList_own_empty { p with refcount := p.refcount + 1 }
  · exact erasePeerList_identity _ { p with refcount := p.refcount + 1 }

end Leanux.Proofs.WG.Config
