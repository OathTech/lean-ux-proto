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
      WGPEER_F_REPLACE_ALLOWEDIPS none pid) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some
        (withPeer removed pid { (erasePeerList p.allowedipsList p) with refcount := p.refcount - 1 })) := by
  let q := erasePeerList p.allowedipsList p
  have peer : removed.peers[pid]? = some q := by
    simpa [resident, q] using removalEffect_peers steps pid
  have count : q.refcount = p.refcount := erasePeerList_refcount _ _
  have running : removed.running = false := (removalEffect_running steps).trans down
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .peerRemoveMe false)
    .peerSetPsk false) .peerHasEndpoint false) .peerReplaceAips true
  obtain ⟨done, middle, a1, removeRun, changed⟩ :=
    removeByPeer_general pid p d removed resident steps g before device
  cases done
  obtain ⟨ret, final, after, tailRun, result, released⟩ :=
    replacementTail_down key pid removed q peer (by simpa [count] using retained)
      running middle a1 changed
  refine ⟨ret, final, after, ?_, result, ?_⟩
  · have removeOff : (2 : UInt32) &&& 1 = 0 := by decide
    simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS,
      WGPEER_F_REMOVE_ME, branch, AmbientM.branch, removeOff]
    rw [show ((removeByPeer pid).run g).run before = .ok (((), middle), a1) from removeRun]
    exact tailRun
  · simpa [q, erasePeerList_refcount] using released

def generalReplacementDevice (removed : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer removed pid
    { (erasePeerList p.allowedipsList { p with refcount := p.refcount + 1 }) with refcount := p.refcount }

theorem setPeer_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Returns (setPeerCmd (replaceAllowedipsAttrs key)) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some (generalReplacementDevice removed pid p)) := by
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
    replacementUpdate_general key pid acquiredDevice removed acquired
      (by simp [acquiredDevice, withPeer]) (by simpa [acquired] using live) down steps
      middle (mark a1 .peerNotFound false) acquiredState
  refine ⟨ret, final, after, ?_, value, ?_⟩
  · have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
    rw [← setPeerCmd_source]
    simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS,
      WG.andM, branch, AmbientM.branch, good]
    rw [show ((pubkeyLookup key).run g).run before = .ok ((some pid, middle), a1) from lookupRun]
    exact updateRun
  · simpa [generalReplacementDevice, acquired] using changed

theorem devicePeers_replace_general (selector : Device) (key : Key) (pid : PeerId)
    (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect (withPeer d pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ devicePeersSource (replaceAllowedipsDeviceAttrs selector key)
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.dev = some (generalReplacementDevice removed pid p)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .setDevHasPeers true) .setDevPeersIter true) .setDevParseErr false
  obtain ⟨ret, final, middle, run, result, changed⟩ :=
    setPeer_replace_general key pid d removed p found peer live bounded down steps g before device
  subst ret
  let after := mark (mark (mark middle .setDevSetPeerErr false) .setDevPeersIter false) .setDevZeroKey false
  refine ⟨0, final, after, ?_, rfl, changed⟩
  simp [devicePeersSource, replaceAllowedipsDeviceAttrs, branch, AmbientM.branch,
    List.forIn_cons, List.forIn_nil]
  rw [show ((setPeerCmd (replaceAllowedipsAttrs key)).run g).run before =
    .ok ((0, final), middle) from run]
  rfl

theorem setDevice_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect
      (withPeer { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.dev = some (generalReplacementDevice removed pid p)) := by
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
      (fun ret g => ret = 0 ∧ g.dev = some (generalReplacementDevice removed pid p)) := by
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
      (devicePeers_replace_general d key pid updated removed p found peer live bounded down steps)
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine returns_bind _ _ ((returns_iff _ _ _).mpr (lookupInterface_index d)) ?_
  intro ret g ambient pre
  obtain ⟨rfl, device⟩ := pre
  simpa [replaceAllowedipsDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using tail g ambient device

theorem generalReplacement_peer (removed : Device) (pid : PeerId) (p : Peer) :
    ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
      q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId := by
  refine ⟨{ (erasePeerList p.allowedipsList { p with refcount := p.refcount + 1 }) with
    refcount := p.refcount }, by simp [generalReplacementDevice, withPeer], ?_, rfl, ?_⟩
  · exact erasePeerList_own_empty { p with refcount := p.refcount + 1 }
  · exact erasePeerList_identity _ { p with refcount := p.refcount + 1 }

end Leanux.Proofs.WG.Config
