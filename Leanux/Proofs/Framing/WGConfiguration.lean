import Leanux.Proofs.Framing.WGHandshake
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Netlink

/-! Configuration-only device mutations. The full Kernel mask retains device
presence, every resident object and allocator frontier. These leaves inspect
only device fields/scalar IDs; the original pending-worker helper is a no-op.
Access coverage is audited separately from these normal-endpoint frames. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def configurationDevice (d : Device) : Device :=
  {d with staticIdentity := {}, cookieEncryptionKey := [], mac1Key := [], deviceUpdateGen := 0, fwmark := 0}
def configurationKernel (k : Kernel) : Kernel :=
  {k with wg := k.wg.map configurationDevice}
def configurationView (w : World) : Kernel := configurationKernel w.k
abbrev SameConfiguration (a : M α) := SameView configurationView a

theorem modifyDev_configuration_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, configurationDevice (f d) = configurationDevice d) :
    ⦃fun w => ⌜P (configurationView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (configurationView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [configurationView, configurationKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem setStaticIdentityPrivateKey_sameConfiguration (key : Key) :
    SameConfiguration (setStaticIdentityPrivateKey key) := by
  apply SameView.of_wp
  intro s
  have hg := (SameView.of_sameKernel configurationKernel (generatePublic_sameKernel key)).wp (fun t => t = s)
  have hm := modifyDev_configuration_spec (fun t => t = s)
  have hl (α β : Type) := list_view_spec configurationView (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, setStaticIdentityPrivateKey, getDev, getK, requireNotPending, invariant, hg, hm]
  all_goals intros; rfl

theorem cookiePrecomputeDeviceKeys_sameConfiguration :
    SameConfiguration cookiePrecomputeDeviceKeys := by
  apply SameView.of_wp
  intro s
  have hm := modifyDev_configuration_spec (fun t => t = s)
  mvcgen [cookiePrecomputeDeviceKeys, getDev, getK, invariant, branch, hm]
  all_goals intros; rfl

theorem netDevices_sameKernel : SameKernel netDevices := by
  apply sameKernel_of_wp
  intro k
  mvcgen [netDevices, getK]

theorem lookupInterface_sameKernel (ref : DeviceRef) : SameKernel (lookupInterface ref) := by
  apply sameKernel_of_wp
  intro k
  have hn := sameKernel_wp _ netDevices_sameKernel (fun t => t = k)
  mvcgen [lookupInterface, hn, branch, WG.orM, invariant]

end Leanux.Proofs.Framing
