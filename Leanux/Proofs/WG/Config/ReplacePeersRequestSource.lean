import Leanux.Proofs.WG.Config.RemoveAllObservationSource
import Leanux.Proofs.WG.Config.DeviceSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def replacePeersAttrs (selector : DeviceRef) : DeviceAttrs :=
  { device := selector, flags := some WGDEVICE_F_REPLACE_PEERS }

private def replacePeersPrefix (selector : DeviceRef) : WG.M (Except Int Unit) := do
  let selected ← lookupInterface selector
  if ← branch .setDevLookupErr (selected matches .error _) then
    let .error e := selected | invariant "unreachable"
    _ ← branch .setDevZeroKey false
    return .error e
  _ ← branch .setDevHasFlags true
  _ ← branch .setDevBadFlags false
  _ ← branch .setDevHasPort false
  _ ← branch .setDevHasFwmark false
  modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  _ ← branch .setDevFwmark false
  _ ← branch .setDevPort false
  _ ← branch .setDevReplacePeers true
  return .ok ()

private def replacePeersSuffix : WG.M Int := do
  _ ← branch .setDevHasPrivateKey false
  _ ← branch .setDevHasPeers false
  _ ← branch .setDevZeroKey false
  return 0

/-- The actual native prefix and suffix surround one arbitrary Product callback.
Selection errors return before generation and removal. -/
def replacePeersWith {α : Type} (selector : DeviceRef) (remove : Leanux.M α) : Leanux.M (Option α × Int) := do
  let selected ← liftWG (replacePeersPrefix selector)
  match selected with
  | .error e => return (none, e)
  | .ok () =>
    let cut ← remove
    let result ← liftWG replacePeersSuffix
    return (some cut, result)

theorem replacePeersWith_source (selector : DeviceRef) :
    (do let result ← replacePeersWith selector (liftWG peerRemoveAll); pure result.2) =
      liftWG (wgSetDevice (replacePeersAttrs selector)) := by
  let log (site : Decision) (value : Bool) : WG.M Unit := discard (branch site value)
  have logged (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do log site value; pure value) := by
    funext g ambient
    rfl
  have native : wgSetDevice (replacePeersAttrs selector) = (do
      let selected ← replacePeersPrefix selector
      match selected with
      | .error e => return e
      | .ok () => peerRemoveAll; replacePeersSuffix) := by
    have valid : WGDEVICE_F_REPLACE_PEERS &&& ~~~WGDEVICE_F_ALL = 0 := by decide
    have nonzero : (WGDEVICE_F_REPLACE_PEERS != 0) = true := by decide
    rw [← wgSetDevice_source]
    simp only [wgSetDeviceSource, replacePeersPrefix, replacePeersAttrs,
      deviceUpdateSource, deviceKeySource, devicePeersSource, replacePeersSuffix, WG.andM, WG.orM,
      logged, bind_assoc, pure_bind]
    apply congrArg (fun (next : Except Int Unit → WG.M Int) => lookupInterface selector >>= next)
    funext selected
    cases selected <;> simp [valid, nonzero, bind_assoc]
  have lift_bind {α β : Type} (a : WG.M α) (f : α → WG.M β) :
      liftWG (a >>= f) = (liftWG a >>= fun x => liftWG (f x)) := by
    funext w
    dsimp only [liftWG, StateT.run, StateT.bind, StateT.pure, StateT.map,
      Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
    cases run : a w.wg w.ambient with
    | error err => rfl
    | ok pair => rcases pair with ⟨⟨out, current⟩, after⟩; rfl
  have lift_pure {α : Type} (x : α) : liftWG (pure x : WG.M α) = pure x := rfl
  rw [native]
  simp only [replacePeersWith, lift_bind, bind_assoc]
  congr 1
  funext selected
  cases selected with
  | error e => simp only [pure_bind, lift_pure]
  | ok u => cases u; simp only [lift_bind, bind_assoc, pure_bind, bind_pure]

def observedReplacePeers (selector : DeviceRef) : Leanux.M (Option RemoveAllCall × Int) :=
  replacePeersWith selector observedRemoveAll

theorem observedReplacePeers_erase (selector : DeviceRef) :
    (do let result ← observedReplacePeers selector; pure result.2) =
      liftWG (wgSetDevice (replacePeersAttrs selector)) := by
  have drop {α : Type} (remove : Leanux.M α) :
      (do let result ← replacePeersWith selector remove; pure result.2) =
        (do let result ← replacePeersWith selector (do let _ ← remove; pure ()); pure result.2) := by
    simp only [replacePeersWith, bind_assoc]
    congr 1
    funext selected
    cases selected with
    | error e => rfl
    | ok u => cases u; simp only [bind_assoc, pure_bind]
  rw [observedReplacePeers, drop, observedRemoveAll_erase]
  exact replacePeersWith_source selector

end Leanux.Proofs.WG.Config
