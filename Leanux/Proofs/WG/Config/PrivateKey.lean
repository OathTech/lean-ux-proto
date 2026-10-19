import Leanux.Proofs.WG.Config.Identity
import Leanux.Proofs.WG.Config.DeviceScalars

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def cookieKeysAfter (d : Device) : Device :=
  { d with
    cookieEncryptionKey := if d.staticIdentity.hasIdentity then
      blake2s 32 [] ("cookie--".toUTF8.toList ++ d.staticIdentity.staticPublic)
      else List.replicate 32 0
    mac1Key := if d.staticIdentity.hasIdentity then
      blake2s 32 [] ("mac1----".toUTF8.toList ++ d.staticIdentity.staticPublic)
      else List.replicate 32 0 }

theorem cookiePrecompute_run (d : Device) (g : WGWorld) (ambient : Ambient)
    (device : g.dev=some d) :
    ((cookiePrecomputeDeviceKeys).run g).run ambient =
      .ok (((),{g with dev:=some (cookieKeysAfter d)}),
        {ambient with steps:=ambient.steps.push {
          decision:=.cookieDeviceHasIdentity,outcome:=d.staticIdentity.hasIdentity,
          netRx:=ambient.netRxSection}}) := by
  cases has : d.staticIdentity.hasIdentity
  all_goals simp [cookiePrecomputeDeviceKeys,getDev,device,modifyDev,
    branch,AmbientM.branch,has,cookieKeysAfter]
  all_goals rfl

theorem setStaticIdentity_run (key : Key) (d : Device) (g : WGWorld) (ambient : Ambient)
    (device : g.dev=some d) :
    ((setStaticIdentityPrivateKey key).run g).run ambient =
      .ok (((),{g with dev:=some {d with staticIdentity:=identityAfter key d.staticIdentity}}),
        {ambient with steps:=ambient.steps.push {
          decision:=.genPublicNullSecret,outcome:=key==nullPoint,
          netRx:=ambient.netRxSection}}) := by
  have idle (peers : List PeerId) :
      List.foldlM (fun (_ : Unit) pid => requireNotPending pid "changing the device identity") () peers =
        (pure () : WG.M Unit) := by
    induction peers with
    | nil => rfl
    | cons pid peers ih => simpa only [List.foldlM_cons,requireNotPending,pure_bind] using ih
  cases null : key==nullPoint
  all_goals simp [setStaticIdentityPrivateKey,idle,getDev,device,generatePublic,
    branch,AmbientM.branch,null,modifyDev,identityAfter]
  all_goals rfl

theorem cookiePrecompute_returns (d : Device) :
    Returns cookiePrecomputeDeviceKeys (fun g => g.dev = some d)
      (fun _ g => g.dev = some (cookieKeysAfter d)) := by
  intro g ambient device
  exact ⟨(),_,_,cookiePrecompute_run d g ambient device,rfl⟩

theorem setStaticIdentity_returns (key : Key) (d : Device) :
    Returns (setStaticIdentityPrivateKey key) (fun g => g.dev = some d)
      (fun _ g => g.dev = some { d with staticIdentity := identityAfter key d.staticIdentity }) := by
  intro g ambient device
  exact ⟨(),_,_,setStaticIdentity_run key d g ambient device,rfl⟩

def privateKeyAttrs (d : Device) (key : Key) : DeviceAttrs :=
  { device := byIndex d, privateKey := some key }

theorem setDevice_private_unchanged (d : Device) (key : Key)
    (same : d.staticIdentity.staticPrivate = key) :
    Returns (wgSetDevice (privateKeyAttrs d key))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun ret g => ret = 0 ∧ g.dev = some { d with deviceUpdateGen := d.deviceUpdateGen + 1 }) := by
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
  have keyTail : Returns (deviceKeySource (privateKeyAttrs d key))
      (fun g => g.dev = some updated)
      (fun ret g => ret = 0 ∧ g.dev = some updated) := by
    intro g ambient device
    let logged (a : Ambient) (site : Decision) (value : Bool) :=
      {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
    let after := logged (logged (logged (logged (logged ambient
      .setDevHasPrivateKey true) .setDevPrivateKeyLen true) .setDevKeyUnchanged true)
      .setDevHasPeers false) .setDevZeroKey true
    refine ⟨0, g, after, ?_, rfl, device⟩
    simp [deviceKeySource, devicePeersSource, privateKeyAttrs, WG.andM, getDev,
      device, updated, same, branch, AmbientM.branch, after, logged]
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
      deviceKeySource (privateKeyAttrs d key))
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some updated) := by
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ hu (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact returns_bind _ _ (hm _ _ updated) (fun _ => keyTail)
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine returns_bind _ _ ((returns_iff _ _ _).mpr (lookupInterface_index d)) ?_
  intro ret g ambient pre
  obtain ⟨rfl, device⟩ := pre
  simpa [privateKeyAttrs, deviceUpdateSource, WG.orM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using tail g ambient device

end Leanux.Proofs.WG.Config
