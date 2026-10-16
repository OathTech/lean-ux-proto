import Leanux.Proofs.Framing.WGHandshake
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Netlink

/-! Configuration-only device mutations retain the eleven WG-owned observations
outside their explicit device mask. Resident objects and allocator frontiers
remain visible; these normal-return contracts impose no Ambient restriction. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def configurationDevice (d : Device) : Device :=
  {d with staticIdentity := {}, cookieEncryptionKey := [], mac1Key := [], deviceUpdateGen := 0, fwmark := 0}

def configurationView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with dev := g.dev.map configurationDevice}

abbrev SameConfiguration (a : WG.M α) := SameView configurationView a

theorem modifyDev_configuration_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, configurationDevice (f d) = configurationDevice d) :
    ⦃fun w => ⌜P (configurationView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (configurationView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [configurationView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem setStaticIdentityPrivateKey_sameConfiguration (key : Key) :
    SameConfiguration (setStaticIdentityPrivateKey key) := by
  apply SameView.of_wp
  intro s
  have hg := ((generatePublic_sameWGWorld key).factor configurationView).wp (fun t => t = s)
  have hm := modifyDev_configuration_spec (fun t => t = s)
  have hl (α β : Type) := list_view_spec configurationView (m := AmbientM)
    (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    setStaticIdentityPrivateKey, getDev, requireNotPending, invariant, AmbientM.invariant, hg, hm]
  all_goals intros; rfl

theorem cookiePrecomputeDeviceKeys_sameConfiguration :
    SameConfiguration cookiePrecomputeDeviceKeys := by
  apply SameView.of_wp
  intro s
  have hm := modifyDev_configuration_spec (fun t => t = s)
  mvcgen [cookiePrecomputeDeviceKeys, getDev, invariant, AmbientM.invariant,
    branch, AmbientM.branch, hm]
  all_goals intros; rfl

theorem netDevices_sameWGWorld : SameView (id : WGWorld → WGWorld) netDevices := by
  apply SameView.of_wp
  intro initial
  mvcgen [netDevices]

theorem lookupInterface_sameWGWorld (ref : DeviceRef) :
    SameView (id : WGWorld → WGWorld) (lookupInterface ref) := by
  apply SameView.of_wp
  intro initial
  have hn := netDevices_sameWGWorld.wp (fun t => t = initial)
  mvcgen [lookupInterface, hn, branch, AmbientM.branch, WG.orM, invariant, AmbientM.invariant]

end Leanux.Proofs.Framing
