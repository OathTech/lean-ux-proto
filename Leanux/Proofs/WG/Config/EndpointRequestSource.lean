import Leanux.Proofs.WG.Config.EndpointAttributeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

theorem devicePeers_endpoint (selector d : Device) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (devicePeersSource (endpointDeviceAttrs selector key a updateOnly bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ ∃ reset,
        g.dev = some (endpointSetterDevice d pid p a reset) ∧ readbackFrame g sock fixtures) := by
  intro g ambient ret final after pre run
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .setDevHasPeers true) .setDevPeersIter true) .setDevParseErr false
  cases executed : ((setPeerCmd (endpointPeerAttrs key a updateOnly)).run g).run before with
  | error stop =>
    cases bad <;> simp [devicePeersSource, endpointDeviceAttrs, branch, AmbientM.branch,
      before, mark, executed] at run
    all_goals change (Except.error stop : Except Stop _) = .ok ((ret, final), after) at run
    all_goals cases run
  | ok output =>
    obtain ⟨⟨value, middle⟩, next⟩ := output
    obtain ⟨code, reset, device, frame⟩ := setPeer_endpoint_down key a updateOnly pid d p
      found resident live bounded down sock fixtures g before value middle next pre executed
    subst value
    cases bad <;> simp [devicePeersSource, endpointDeviceAttrs, branch, AmbientM.branch,
      before, mark, executed] at run
    all_goals dsimp only [Bind.bind, Except.bind] at run
    all_goals obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    all_goals exact ⟨rfl, reset, device, frame⟩

/-- The full request increments the device generation before the endpoint
request. A later malformed peer retains all preceding writes. -/
theorem setDevice_endpoint (d : Device) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (endpointDeviceAttrs d key a updateOnly bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ ∃ reset,
        g.dev = some (endpointSetterDevice {d with deviceUpdateGen := d.deviceUpdateGen + 1} pid p a reset) ∧
        readbackFrame g sock fixtures) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Ensures (mark site value)
        (fun g => g.dev = some entry ∧ readbackFrame g sock fixtures)
        (fun _ g => g.dev = some entry ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hu : Ensures (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => g.dev = some updated ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    simp [modifyDev, pre.1] at run
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    exact ⟨rfl, pre.2⟩
  have tail : Ensures (do
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
      devicePeersSource (endpointDeviceAttrs d key a updateOnly bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ ∃ reset,
        g.dev = some (endpointSetterDevice updated pid p a reset) ∧ readbackFrame g sock fixtures) := by
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ hu (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact devicePeers_endpoint d updated key a updateOnly bad pid p sock fixtures
      found resident live bounded down
  have lookup : Ensures (lookupInterface (byIndex d))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun selected g => selected = .ok () ∧ g.dev = some d ∧ readbackFrame g sock fixtures) := by
    intro g ambient selected final after pre run
    obtain ⟨value, middle, next, closed, facts⟩ :=
      (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g ambient pre
    rw [closed] at run
    cases run
    exact facts
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine ensures_bind _ _ lookup ?_
  intro selected g ambient ret final after pre
  obtain ⟨rfl, device, frame⟩ := pre
  simpa [endpointDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using
    tail g ambient ret final after ⟨device, frame⟩

end Leanux.Proofs.WG.Config
