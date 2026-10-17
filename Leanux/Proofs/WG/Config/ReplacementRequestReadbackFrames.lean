import Leanux.Proofs.WG.Config.ReplacementPeerReadbackFrames
import Leanux.Proofs.WG.Config.ScalarGetterSource
import Leanux.Proofs.WG.Config.RequestModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The actual singleton replacement peer loop preserves both readback fields;
its result-code branch is retained, without a supplied successful execution. -/
theorem devicePeers_replace_readbackFrame (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) :
      Ensures (mark site value) (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
        (fun _ g => g.dev = some d ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  let finish : Int → WG.M Int := fun ret => do
    if ← branch .setDevSetPeerErr (ret < 0) then
      _ ← branch .setDevZeroKey false
      return ret
    _ ← branch .setDevPeersIter false
    _ ← branch .setDevZeroKey false
    pure 0
  have suffix (ret : Int) : Ensures (finish ret) (fun g => readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    by_cases failed : ret < 0
    all_goals
      simp [finish, branch, AmbientM.branch, failed] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have body : Ensures (do
      mark .setDevHasPeers true
      mark .setDevPeersIter true
      mark .setDevParseErr false
      let ret ← setPeerCmd (replaceAllowedipsAttrs key)
      finish ret)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    refine ensures_bind _ _ (hm _ _) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _) (fun _ => ?_)
    exact ensures_bind _ _ (setPeer_replace_readbackFrame key pid d p sock fixtures
      found resident pairs live bounded down) suffix
  have source : devicePeersSource (replaceAllowedipsDeviceAttrs d key) = (do
      mark .setDevHasPeers true
      mark .setDevPeersIter true
      mark .setDevParseErr false
      let ret ← setPeerCmd (replaceAllowedipsAttrs key)
      finish ret) := by
    simp [devicePeersSource, replaceAllowedipsDeviceAttrs, List.forIn_cons,
      List.forIn_nil, branchSource, finish, bind_assoc]
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext ret
    congr 1
    funext _
    by_cases failed : ret < 0 <;>
      simp [failed, map_eq_pure_bind, bind_assoc, -bind_pure_comp]
  rw [source]
  exact body

/-- A normal original replacement request preserves the getter socket and
fixture-device selector. The actual removal may still stop: the contract makes
no completion claim and assumes no successful-removal witness. -/
theorem setDevice_replace_readbackFrame (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  let updated := requestGeneration d
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Ensures (mark site value) (fun g => g.dev = some entry ∧ readbackFrame g sock fixtures)
        (fun _ g => g.dev = some entry ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hu : Ensures (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => g.dev = some updated ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact ⟨by simp [pre.1, updated, requestGeneration], pre.2⟩
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
      devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
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
    exact devicePeers_replace_readbackFrame key pid updated p sock fixtures
      found resident pairs live bounded down
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  have lookup : Ensures (lookupInterface (byIndex d))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = .ok () ∧ g.dev = some d ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    exact removal_returns_ensures_native
      ((returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures))
      g ambient result final after ⟨pre.1, pre.2.2, pre.2.1⟩ run
  refine ensures_bind _ _ lookup ?_
  intro ret g ambient result final after pre run
  obtain ⟨rfl, device, frame⟩ := pre
  apply tail g ambient result final after ⟨device, frame⟩
  simpa [replaceAllowedipsDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using run

end Leanux.Proofs.WG.Config
