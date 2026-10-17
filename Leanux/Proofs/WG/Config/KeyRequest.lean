import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.KeyCollision
import Leanux.Proofs.WG.Config.ClaimView

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The ordered peer effects use observations from the actual installation run,
including the recorded queued-work decision. No queued-work prediction is made. -/
theorem setDevice_private_changed_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Campaign2.Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ final observations, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key)
          (installedDevice (requestGeneration d) key) d.peerList observations final) := by
  have changedFlag : (d.staticIdentity.staticPrivate == key) = false := by
    simpa only [beq_eq_false_iff_ne] using changed
  let updated := requestGeneration d
  let P : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ ∃ final observations,
    g.dev = some final ∧ ObservedKeyPeerRun (requestsStagedSend d key)
      (installedDevice updated key) d.peerList observations final
  have install : Ensures (keyInstallSource key) (fun g => g.dev = some updated)
      (fun _ g => ∃ final observations, g.dev = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key) (installedDevice updated key)
          d.peerList observations final) := by
    intro g ambient result final after device run
    cases result
    have erased := observedKeyInstallSource_erase key updated g ambient device
    change (((observedKeyInstallSource key).run g).run ambient >>= _) = _ at erased
    rw [run] at erased
    cases observedRun : ((observedKeyInstallSource key).run g).run ambient with
    | error error => rw [observedRun] at erased; cases erased
    | ok pair =>
      obtain ⟨⟨observations, current⟩, inputs⟩ := pair
      rw [observedRun] at erased
      cases erased
      obtain ⟨done, device, effect⟩ := keyInstall_complete updated key
        g ambient observations final after device observedRun
      exact ⟨done, observations, device, effect⟩
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
    obtain ⟨u, current, inputs, collisionRun, currentDevice⟩ :=
      keyCollision_absent updated key (by simpa [updated, noKeyCollision, requestGeneration] using absent)
        g before device
    cases u
    have source : ((devicePrivateSource (privateKeyAttrs d key)).run g).run ambient =
        (((keyInstallSource key).run current).run inputs >>= fun ((_, out), tail) =>
          .ok (((0 : Int), out), logged (logged tail .setDevHasPeers false) .setDevZeroKey true)) := by
      simp [devicePrivateSource, devicePeersSource, privateKeyAttrs, WG.andM, getDev,
        device, updated, requestGeneration, changed, changedFlag, branch, AmbientM.branch]
      rw [collisionRun]
      rfl
    rw [source] at run
    cases installRun : ((keyInstallSource key).run current).run inputs with
    | error error => rw [installRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨u, out⟩, tail⟩ := pair
      rw [installRun] at run
      cases run
      exact ⟨rfl, install current inputs u final tail currentDevice installRun⟩
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
