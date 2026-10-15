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

theorem cookiePrecompute_returns (d : Device) :
    Returns cookiePrecomputeDeviceKeys (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (cookieKeysAfter d)) := by
  rw [returns_iff]
  mvcgen [cookiePrecomputeDeviceKeys, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [cookieKeysAfter]

theorem setStaticIdentity_returns (key : Key) (d : Device) :
    Returns (setStaticIdentityPrivateKey key) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with staticIdentity := identityAfter key d.staticIdentity }) := by
  rw [returns_iff]
  mvcgen [setStaticIdentityPrivateKey, generatePublic, requireNotPending,
    getDev, getK, modifyDev, modifyK, branch, invariant, unsupported]
  invariants
  | inv1 => ((⇓ _ w => ⌜w.k.wg = some d⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [identityAfter]

def privateKeyAttrs (d : Device) (key : Key) : DeviceAttrs :=
  { device := byIndex d, privateKey := some key }

theorem setDevice_private_unchanged (d : Device) (key : Key)
    (same : d.staticIdentity.staticPrivate = key) :
    Returns (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg = some { d with deviceUpdateGen := d.deviceUpdateGen + 1 }) := by
  have hl := lookupInterface_index d
  rw [← wgSetDevice_source, returns_iff]
  simp [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, devicePeersSource,
    privateKeyAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [same]
  all_goals grind only

end Leanux.Proofs.WG.Config
