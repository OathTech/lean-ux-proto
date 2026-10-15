import Leanux.Proofs.WG.Config.AllowedRootFrames
import Leanux.Proofs.WG.Config.AllowedRootRemoval
import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.DeviceScalars

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def replaceAllowedipsAttrs (key : Key) : PeerAttrs :=
  { publicKey := some key, flags := some WGPEER_F_REPLACE_ALLOWEDIPS, allowedIps := some [] }

theorem replacementTail_down (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount) (down : d.running = false) :
    Returns (peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid)
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (withPeer d pid { p with refcount := p.refcount - 1 })) := by
  have hp := peerPut_retained_returns pid d p resident retained
  rw [returns_iff]
  simp [peerConfigTailSource, replaceAllowedipsAttrs]
  mvcgen [getDev, getK, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem replacementUpdate_root (v4 : Bool) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4)
    (retained : 1 < p.refcount) (down : d.running = false) :
    Returns (peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (withPeer (rootLeafRemoved v4 d id n) pid
          { eraseListedPeer id p with refcount := p.refcount - 1 })) := by
  have hr := (returns_iff _ _ _).mp
    (removeByPeer_root v4 d pid p id n peer listed resident leaf parent)
  have ht := (returns_iff _ _ _).mp
    (replacementTail_down key pid (rootLeafRemoved v4 d id n) (eraseListedPeer id p)
      (by simp [rootLeafRemoved_peer, peer]) retained
      (by simpa [rootLeafRemoved_running] using down))
  rw [returns_iff]
  simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS,
    WGPEER_F_REMOVE_ME]
  mvcgen [branch, hr, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [eraseListedPeer]

def rootReplacementDevice (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) : Device :=
  withPeer (rootLeafRemoved v4 (withPeer d pid { p with refcount := p.refcount + 1 }) id n)
    pid (eraseListedPeer id p)

theorem setPeer_replace_root (v4 : Bool) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (rootReplacementDevice v4 d pid p id n)) := by
  have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
  let acquired := { p with refcount := p.refcount + 1 }
  let acquiredDevice := withPeer d pid acquired
  have hl := pubkeyLookup_present_returns key pid d p found peer live bounded
  have hu := (returns_iff _ _ _).mp
    (replacementUpdate_root v4 key pid acquiredDevice acquired id n
      (by simp [acquiredDevice, withPeer]) listed resident leaf parent (by simpa [acquired] using live) down)
  rw [← setPeerCmd_source, returns_iff]
  simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS]
  mvcgen [WG.andM, branch, invariant, hl, hu]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [rootReplacementDevice, acquiredDevice, acquired, eraseListedPeer, withPeer]
  all_goals subst_vars
  all_goals first | exact hu _ (by simp_all) | grind only

theorem rootReplacement_peer (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p) (q : PeerId) :
    (rootReplacementDevice v4 d pid p id n).peers[q]? = d.peers[q]?.map (eraseListedPeer id) := by
  by_cases same : q = pid
  · subst q
    simp [rootReplacementDevice, withPeer, peer]
  · simp [rootReplacementDevice, withPeer, Std.TreeMap.getElem?_insert, Ne.symm same,
      same, rootLeafRemoved_peer]

def RootReplacementEffects (v4 : Bool) (d : Device) (id : NodeId) (final : Device) : Prop :=
  (∀ q : PeerId, final.peers[q]? = d.peers[q]?.map (eraseListedPeer id)) ∧
  (∀ q : NodeId, final.nodes[q]? = if q = id then none else d.nodes[q]?) ∧
  final.peerAllowedips = if v4 then
    { d.peerAllowedips with root4 := none, seq := d.peerAllowedips.seq + 1 }
    else { d.peerAllowedips with root6 := none, seq := d.peerAllowedips.seq + 1 }

theorem rootReplacement_effects (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p) :
    RootReplacementEffects v4 d id (rootReplacementDevice v4 d pid p id n) := by
  refine ⟨rootReplacement_peer v4 d pid p id n peer, ?_, ?_⟩
  · intro q
    simpa [rootReplacementDevice, withPeer] using
      rootLeafRemoved_node v4 (withPeer d pid { p with refcount := p.refcount + 1 }) id n q
  · simpa [rootReplacementDevice, withPeer] using
      rootLeafRemoved_table v4 (withPeer d pid { p with refcount := p.refcount + 1 }) id n

def replaceAllowedipsDeviceAttrs (d : Device) (key : Key) : DeviceAttrs :=
  { device := byIndex d, peers := some [.attrs (replaceAllowedipsAttrs key)] }

theorem devicePeers_replace_root (selector : Device) (v4 : Bool) (key : Key)
    (pid : PeerId) (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ devicePeersSource (replaceAllowedipsDeviceAttrs selector key)
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.k.wg = some (rootReplacementDevice v4 d pid p id n)⌝⦄ := by
  have hp := (returns_iff _ _ _).mp
    (setPeer_replace_root v4 key pid d p id n found peer listed resident leaf parent live bounded down)
  simp [devicePeersSource, replaceAllowedipsDeviceAttrs, List.forIn_cons, List.forIn_nil]
  mvcgen [branch, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem setDevice_replace_root (v4 : Bool) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (rootReplacementDevice v4 { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p id n)) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hp := devicePeers_replace_root d v4 key pid updated p id n
    found peer listed resident leaf parent live bounded down
  rw [← wgSetDevice_source, returns_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, replaceAllowedipsDeviceAttrs]
  mvcgen [WG.orM, WG.andM, branch, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals first | exact hp _ (by simp_all [updated]) | grind only

end Leanux.Proofs.WG.Config
