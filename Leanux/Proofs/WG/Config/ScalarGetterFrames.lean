import Leanux.Proofs.WG.Config.ReadbackFrames

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def scalarDeviceAttrs (d : Device) (key psk : Key) (interval : Nat) (bad : Bool) : DeviceAttrs :=
  { device := byIndex d, peers := some ([.attrs (scalarAttrs key psk interval)] ++
      if bad then [.malformed] else []) }

def scalarRequestDevice (d : Device) (pid : PeerId) (p : Peer) (psk : Key) (interval : Nat) : Device :=
  scalarDevice { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p psk interval

theorem lookupInterface_index_framed (d : Device) (sock : NlSock) (fixtures : FixtureDevices) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures ∧ selectsDevice w d⌝⦄
      lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  obtain ⟨device, framed, selected⟩ := pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let after := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  refine ⟨.ok (), g, after, ?_, rfl, device, framed⟩
  simp [selectsDevice] at selected
  simp [lookupInterface, byIndex, netDevices, device, selected, WG.orM,
    branch, AmbientM.branch, after, mark]
  rfl

theorem devicePeers_scalars_framed (selector d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄
      devicePeersSource (scalarDeviceAttrs selector key psk interval bad)
    ⦃⇓ ret w => ⌜ret = (if bad then -EINVAL else 0) ∧ w.dev = some (scalarDevice d pid p psk interval) ∧
      readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .setDevHasPeers true) .setDevPeersIter true) .setDevParseErr false
  obtain ⟨ret, final, middle, run, result, changed, frame⟩ :=
    setPeer_scalars_down_returns_framed sock fixtures key psk interval pid d p
      found resident live bounded down g before pre
  subst ret
  let after := if bad then
    mark (mark (mark (mark middle .setDevSetPeerErr false)
      .setDevPeersIter true) .setDevParseErr true) .setDevZeroKey false
    else mark (mark (mark middle .setDevSetPeerErr false) .setDevPeersIter false) .setDevZeroKey false
  refine ⟨(if bad then -EINVAL else 0), final, after, ?_, rfl, changed, frame⟩
  cases bad
  all_goals simp [devicePeersSource, scalarDeviceAttrs, branch, AmbientM.branch, List.forIn_cons, List.forIn_nil]
  all_goals rw [show ((setPeerCmd (scalarAttrs key psk interval)).run g).run before =
    .ok ((0, final), middle) from run]
  all_goals rfl

theorem setDevice_scalars_framed (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (scalarDeviceAttrs d key psk interval bad))
      (fun w => w.dev = some d ∧ readbackFrame w sock fixtures ∧ selectsDevice w d)
      (fun ret w => ret = (if bad then -EINVAL else 0) ∧ w.dev = some (scalarRequestDevice d pid p psk interval) ∧
        readbackFrame w sock fixtures) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Returns (mark site value)
        (fun g => g.dev = some entry ∧ readbackFrame g sock fixtures)
        (fun _ g => g.dev = some entry ∧ readbackFrame g sock fixtures) := by
    intro g ambient pre
    exact ⟨(), g, {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}}, rfl, pre⟩
  have hu : Returns (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => g.dev = some updated ∧ readbackFrame g sock fixtures) := by
    intro g ambient pre
    refine ⟨(), {g with dev := some updated}, ambient, ?_, rfl, pre.2⟩
    simp [modifyDev, pre.1, updated]
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
      devicePeersSource (scalarDeviceAttrs d key psk interval bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧
        g.dev = some (scalarRequestDevice d pid p psk interval) ∧ readbackFrame g sock fixtures) := by
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
      (devicePeers_scalars_framed d updated key psk interval bad pid p sock fixtures
        found resident live bounded down)
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine returns_bind _ _ ((returns_iff _ _ _).mpr
    (lookupInterface_index_framed d sock fixtures)) ?_
  intro ret g ambient pre
  obtain ⟨rfl, device, frame⟩ := pre
  simpa [scalarDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using
    tail g ambient ⟨device, frame⟩

end Leanux.Proofs.WG.Config
