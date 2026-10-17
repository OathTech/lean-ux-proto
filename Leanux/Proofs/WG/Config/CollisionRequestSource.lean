import Leanux.Proofs.WG.Config.CollisionRemovalSource
import Leanux.Proofs.WG.Config.CollisionObservationModel
import Leanux.Proofs.WG.Config.KeyCollision
import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Config.ScalarReturns

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem keyCollision_present_effect (d : Device) (key pub : Key) (pid : PeerId) (p : Peer)
    (generated : publicResult key = (some pub, true))
    (found : d.peerHashtable.find? (·.1 == pub) = some (pub, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (keyCollisionSource key) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
  let acquired := withPeer d pid { p with refcount := p.refcount + 1 }
  have hg : Ensures (generatePublic key) (fun w => w.dev = some d)
      (fun result w => result = (some pub, true) ∧ w.dev = some d) := by
    intro w ambient result out after pre run
    have actual := removal_returns_ensures_native (generatePublic_return key d) w ambient result out after pre run
    simpa only [generated] using actual
  have hl := removal_returns_ensures_native ((returns_iff _ _ _).mpr
    (pubkeyLookup_present_returns pub pid d p found resident live bounded))
  have hp : Ensures (peerPut (some pid)) (fun w => w.dev = some acquired)
      (fun _ w => w.dev = some (collisionLookupDevice d pid p)) := by
    intro w ambient result out after pre run
    have actual := removal_returns_ensures_native ((returns_iff _ _ _).mpr
      (peerPut_retained_returns pid acquired { p with refcount := p.refcount + 1 }
        (by simp [acquired, withPeer]) (by simpa using live))) w ambient result out after pre run
    simpa [collisionLookupDevice, acquired] using actual
  have hr := peerRemove_live_effect_pairs pid (collisionLookupDevice d pid p) p
    (by simp [collisionLookupDevice, withPeer]) pairs live count send clear
  have putRemove := ensures_bind _ _ hp (fun _ => hr)
  have afterLookup : Ensures (do
      if ← branch .setDevOldPeer (some pid).isSome then
        peerPut (some pid)
        peerRemove (some pid)) (fun w => w.dev = some acquired)
      (fun _ w => ∃ final, w.dev = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ (Q := fun result w => result = true ∧ w.dev = some acquired) ?_ ?_
    · intro g ambient result final after device run
      cases run
      exact ⟨rfl, device⟩
    · intro result w ambient u out after pre run
      obtain ⟨rfl, device⟩ := pre
      exact putRemove w ambient u out after device run
  have lookup : Ensures (do
      let peer ← pubkeyLookup pub
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ hl ?_
    intro result w ambient u out after pre run
    obtain ⟨rfl, device⟩ := pre
    exact afterLookup w ambient u out after device run
  have afterPublic : Ensures (do
      if ← branch .setDevGenPublic true then
        let peer ← pubkeyLookup pub
        if ← branch .setDevOldPeer peer.isSome then
          peerPut peer
          peerRemove peer) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ (Q := fun result w => result = true ∧ w.dev = some d) ?_ ?_
    · intro g ambient result final after device run
      cases run
      exact ⟨rfl, device⟩
    · intro result w ambient u out after pre run
      obtain ⟨rfl, device⟩ := pre
      exact lookup w ambient u out after device run
  unfold keyCollisionSource
  refine ensures_bind _ _ hg ?_
  intro result w ambient u out after pre run
  obtain ⟨rfl, device⟩ := pre
  exact afterPublic w ambient u out after device run

/-- Compose actual lookup/put/removal before installing from its resulting
Device. The installation relation uses actual observations rather than the
historical queued-work predictor. -/
theorem setDevice_private_collision (d : Device) (key pub : Key) (pid : PeerId) (p : Peer)
    (changed : d.staticIdentity.staticPrivate ≠ key)
    (generated : publicResult key = (some pub, true))
    (found : d.peerHashtable.find? (·.1 == pub) = some (pub, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.wg.device = some final ∧
        ObservedCollisionKeyEffect pid (requestGeneration d) p key final) := by
  have changedFlag : (d.staticIdentity.staticPrivate == key) = false := by
    simpa only [beq_eq_false_iff_ne] using changed
  let updated := requestGeneration d
  let P : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ ∃ final,
    g.dev = some final ∧ ObservedCollisionKeyEffect pid updated p key final
  have install (baseline : Device)
      (removed : CollisionRemovalEffect pid (collisionLookupDevice updated pid p) p baseline) :
      Ensures (keyInstallSource key) (fun g => g.dev = some baseline)
        (fun _ g => ∃ final, g.dev = some final ∧ ObservedCollisionKeyEffect pid updated p key final) := by
    intro g ambient result final after device run
    cases result
    have erased := observedKeyInstallSource_erase key baseline g ambient device
    change (((observedKeyInstallSource key).run g).run ambient >>= _) = _ at erased
    rw [run] at erased
    cases observedRun : ((observedKeyInstallSource key).run g).run ambient with
    | error error => rw [observedRun] at erased; cases erased
    | ok pair =>
      obtain ⟨⟨observations, current⟩, inputs⟩ := pair
      rw [observedRun] at erased
      cases erased
      obtain ⟨done, device, effect⟩ := keyInstall_complete baseline key
        g ambient observations final after device observedRun
      exact ⟨done, device, baseline, observations, removed, effect⟩
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Ensures (mark site value) (fun g => g.dev = some entry)
        (fun _ g => g.dev = some entry) := by
    intro g ambient result final after device run
    cases run
    exact device
  have keyTail : Ensures (devicePrivateSource (privateKeyAttrs d key))
      (fun g => g.dev = some updated) P := by
    intro g ambient result final after device run
    let logged (a : Ambient) (site : Decision) (value : Bool) :=
      {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
    let before := logged (logged (logged ambient .setDevHasPrivateKey true)
      .setDevPrivateKeyLen true) .setDevKeyUnchanged false
    have source : ((devicePrivateSource (privateKeyAttrs d key)).run g).run ambient =
        (((keyCollisionSource key).run g).run before >>= fun ((_, current), inputs) =>
          ((keyInstallSource key).run current).run inputs >>= fun ((_, out), tail) =>
            .ok (((0 : Int), out), logged (logged tail .setDevHasPeers false) .setDevZeroKey true)) := by
      simp [devicePrivateSource, devicePeersSource, privateKeyAttrs, WG.andM, getDev,
        device, updated, requestGeneration, changed, changedFlag, branch, AmbientM.branch]
      rfl
    rw [source] at run
    cases collisionRun : ((keyCollisionSource key).run g).run before with
    | error error => rw [collisionRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨u, current⟩, inputs⟩ := pair
      obtain ⟨baseline, currentDevice, removed⟩ :=
        keyCollision_present_effect updated key pub pid p
          generated found resident pairs live bounded count send clear
          g before u current inputs device collisionRun
      rw [collisionRun] at run
      change (((keyInstallSource key).run current).run inputs >>= _) = _ at run
      cases installRun : ((keyInstallSource key).run current).run inputs with
      | error error => rw [installRun] at run; cases run
      | ok pair =>
        obtain ⟨⟨u, out⟩, tail⟩ := pair
        rw [installRun] at run
        cases run
        exact ⟨rfl, install baseline removed current inputs u final tail currentDevice installRun⟩
  have hu : Ensures (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d) (fun _ g => g.dev = some updated) := by
    intro g ambient result final after device run
    cases run
    simp [device, updated, requestGeneration]
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
      devicePrivateSource (privateKeyAttrs d key))
      (fun g => g.dev = some d) P := by
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ hu (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact keyTail
  change Ensures _ (fun g => g.dev = some d ∧ selectsDevice g d) P
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  have lookup : Ensures (lookupInterface (byIndex d))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun result g => result = .ok () ∧ g.dev = some d) := by
    intro g ambient result final after pre run
    obtain ⟨value, out, ending, actual, effect⟩ :=
      (returns_iff _ _ _).mpr (lookupInterface_index d) g ambient pre
    rw [run] at actual
    cases actual
    exact effect
  refine ensures_bind _ _ lookup ?_
  intro result g ambient ret final after pre run
  obtain ⟨rfl, device⟩ := pre
  apply tail g ambient ret final after device
  simpa [privateKeyAttrs, deviceUpdateSource, ← devicePrivate_source, WG.orM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using run


end Leanux.Proofs.WG.Config
