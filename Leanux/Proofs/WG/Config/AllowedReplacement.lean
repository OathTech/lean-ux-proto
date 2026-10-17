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
      (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some (withPeer d pid { p with refcount := p.refcount - 1 })) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .peerHasAips true)
    .peerAipsIter false) .peerHasKeepalive false) .peerRunning false
  obtain ⟨done, final, middle, putRun, changed⟩ :=
    (returns_iff _ _ _).mpr (peerPut_retained_returns pid d p resident retained) g before device
  cases done
  refine ⟨0, final, mark middle .peerZeroPsk false, ?_, rfl, changed⟩
  simp [peerConfigTailSource, replaceAllowedipsAttrs, branch, AmbientM.branch,
    List.forIn_nil, getDev, device, down]
  rw [show ((peerPut (some pid)).run g).run before = .ok (((), final), middle) from putRun]
  rfl

theorem replacementUpdate_root (v4 : Bool) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4)
    (retained : 1 < p.refcount) (down : d.running = false) :
    Returns (peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some
        (withPeer (rootLeafRemoved v4 d id n) pid
          { eraseListedPeer id p with refcount := p.refcount - 1 })) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .peerRemoveMe false)
    .peerSetPsk false) .peerHasEndpoint false) .peerReplaceAips true
  obtain ⟨done, middle, a1, removeRun, removed⟩ :=
    removeByPeer_root v4 d pid p id n peer listed resident leaf parent g before device
  cases done
  obtain ⟨ret, final, after, tailRun, result, changed⟩ :=
    replacementTail_down key pid (rootLeafRemoved v4 d id n) (eraseListedPeer id p)
      (by simp [rootLeafRemoved_peer, peer]) retained
      (by simpa [rootLeafRemoved_running] using down) middle a1 removed
  refine ⟨ret, final, after, ?_, result, changed⟩
  have removeOff : (2 : UInt32) &&& 1 = 0 := by decide
  simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS,
    WGPEER_F_REMOVE_ME, branch, AmbientM.branch, removeOff]
  rw [show ((removeByPeer pid).run g).run before = .ok (((), middle), a1) from removeRun]
  exact tailRun

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
    Returns (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some (rootReplacementDevice v4 d pid p id n)) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark ambient
    .peerHasPubkey true) .peerPubkeyLen true) .peerHasPsk false)
    .peerHasFlags true) .peerBadFlags false) .peerHasProtocol false
  let acquired := {p with refcount := p.refcount + 1}
  let acquiredDevice := withPeer d pid acquired
  obtain ⟨got, middle, a1, lookupRun, result, acquiredState⟩ :=
    (returns_iff _ _ _).mpr (pubkeyLookup_present_returns key pid d p found peer live bounded)
      g before device
  subst got
  obtain ⟨ret, final, after, updateRun, value, changed⟩ :=
    replacementUpdate_root v4 key pid acquiredDevice acquired id n
      (by simp [acquiredDevice, withPeer]) listed resident leaf parent
      (by simpa [acquired] using live) down middle (mark a1 .peerNotFound false) acquiredState
  refine ⟨ret, final, after, ?_, value, ?_⟩
  · have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
    rw [← setPeerCmd_source]
    simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS,
      WG.andM, branch, AmbientM.branch, good]
    rw [show ((pubkeyLookup key).run g).run before = .ok ((some pid, middle), a1) from lookupRun]
    exact updateRun
  · simpa [rootReplacementDevice, acquiredDevice, acquired, eraseListedPeer] using changed

theorem rootReplacement_peer (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p) (q : PeerId) :
    (rootReplacementDevice v4 d pid p id n).peers[q]? = d.peers[q]?.map (eraseListedPeer id) := by
  by_cases same : q = pid
  · subst q
    simp [rootReplacementDevice, withPeer, peer]
  · simp [rootReplacementDevice, withPeer, Std.TreeMap.getElem?_insert, Ne.symm same,
      rootLeafRemoved_peer]

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
    ⦃fun w => ⌜w.dev = some d⌝⦄ devicePeersSource (replaceAllowedipsDeviceAttrs selector key)
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.dev = some (rootReplacementDevice v4 d pid p id n)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .setDevHasPeers true) .setDevPeersIter true) .setDevParseErr false
  obtain ⟨ret, final, middle, run, result, changed⟩ :=
    setPeer_replace_root v4 key pid d p id n found peer listed resident leaf parent live bounded down
      g before device
  subst ret
  let after := mark (mark (mark middle .setDevSetPeerErr false) .setDevPeersIter false) .setDevZeroKey false
  refine ⟨0, final, after, ?_, rfl, changed⟩
  simp [devicePeersSource, replaceAllowedipsDeviceAttrs, branch, AmbientM.branch,
    List.forIn_cons, List.forIn_nil]
  rw [show ((setPeerCmd (replaceAllowedipsAttrs key)).run g).run before =
    .ok ((0, final), middle) from run]
  rfl

theorem setDevice_replace_root (v4 : Bool) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.dev = some
        (rootReplacementDevice v4 { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p id n)) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Returns (mark site value) (fun g => g.dev = some entry)
        (fun _ g => g.dev = some entry) := by
    intro g ambient device
    exact ⟨(), g, {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}}, rfl, device⟩
  have hu : Returns (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d) (fun _ g => g.dev = some updated) := by
    intro g ambient device
    refine ⟨(), {g with dev := some updated}, ambient, ?_, rfl⟩
    simp [modifyDev, device, updated]
    rfl
  have tail : Returns (do
      mark .setDevLookupErr false
      mark .setDevHasFlags false
      mark .setDevBadFlags false
      mark .setDevHasPort false
      mark .setDevHasFwmark false
      modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}
      mark .setDevFwmark false
      mark .setDevPort false
      mark .setDevReplacePeers false
      mark .setDevHasPrivateKey false
      devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some (rootReplacementDevice v4 updated pid p id n)) := by
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ hu (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact (returns_iff _ _ _).mpr
      (devicePeers_replace_root d v4 key pid updated p id n found peer listed resident leaf parent live bounded down)
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine returns_bind _ _ ((returns_iff _ _ _).mpr (lookupInterface_index d)) ?_
  intro ret g ambient pre
  obtain ⟨rfl, device⟩ := pre
  simpa [replaceAllowedipsDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using tail g ambient device

end Leanux.Proofs.WG.Config
