import Leanux.Proofs.WG.Config.RemoveAllObservationSource
import Leanux.Proofs.WG.Config.DeviceSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def replacePeersAttrs (selector : DeviceRef) : DeviceAttrs :=
  { device := selector, flags := some WGDEVICE_F_REPLACE_PEERS }

/-- The original flag-only request, parameterized at its one removal call.
Selection errors return before generation/removal; every original test is kept. -/
def replacePeersWith {α : Type} (selector : DeviceRef) (remove : M α) : M (Option α × Int) := do
  let selected ← lookupInterface selector
  if ← branch .setDevLookupErr (selected matches .error _) then
    let .error e := selected | invariant "unreachable"
    _ ← branch .setDevZeroKey false
    return (none, e)
  _ ← branch .setDevHasFlags true
  _ ← branch .setDevBadFlags false
  _ ← branch .setDevHasPort false
  _ ← branch .setDevHasFwmark false
  modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  _ ← branch .setDevFwmark false
  _ ← branch .setDevPort false
  _ ← branch .setDevReplacePeers true
  let cut ← remove
  _ ← branch .setDevHasPrivateKey false
  _ ← branch .setDevHasPeers false
  _ ← branch .setDevZeroKey false
  return (some cut, 0)

theorem replacePeersWith_source (selector : DeviceRef) :
    (do let result ← replacePeersWith selector peerRemoveAll; pure result.2) =
      wgSetDevice (replacePeersAttrs selector) := by
  have valid : WGDEVICE_F_REPLACE_PEERS &&& ~~~WGDEVICE_F_ALL = 0 := by decide
  have nonzero : (WGDEVICE_F_REPLACE_PEERS != 0) = true := by decide
  rw [← wgSetDevice_source]
  simp only [replacePeersWith, wgSetDeviceSource, replacePeersAttrs, bind_assoc]
  apply congrArg (fun (next : Except Int Unit → M Int) => lookupInterface selector >>= next)
  funext selected
  cases selected with
  | error e =>
    simp [branch, bind_assoc, deviceUpdateSource, deviceKeySource, devicePeersSource,
      WG.andM, WG.orM, valid, nonzero]
  | ok returned =>
    simp [branch, bind_assoc, deviceUpdateSource, deviceKeySource, devicePeersSource,
      WG.andM, WG.orM, valid, nonzero]

def observedReplacePeers (selector : DeviceRef) : M (Option RemoveAllCall × Int) :=
  replacePeersWith selector observedRemoveAll

theorem observedReplacePeers_erase (selector : DeviceRef) :
    (do let result ← observedReplacePeers selector; pure result.2) =
      wgSetDevice (replacePeersAttrs selector) := by
  have drop {α : Type} (remove : M α) :
      (do let result ← replacePeersWith selector remove; pure result.2) =
        (do let result ← replacePeersWith selector (do let _ ← remove; pure ()); pure result.2) := by
    simp only [replacePeersWith, bind_assoc]
    apply congrArg (fun (next : Except Int Unit → M Int) => lookupInterface selector >>= next)
    funext selected
    cases selected <;> simp [branch, bind_assoc]
  rw [observedReplacePeers, drop, observedRemoveAll_erase]
  exact replacePeersWith_source selector

end Leanux.Proofs.WG.Config
