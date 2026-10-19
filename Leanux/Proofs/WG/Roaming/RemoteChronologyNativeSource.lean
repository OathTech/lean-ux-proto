import Leanux.Proofs.WG.Roaming.RemoteChronologyCaptureSource
import Leanux.Proofs.WG.Roaming.RemoteChronologyClassificationSource
import Leanux.Proofs.WG.Roaming.RemoteConfigurationInvariantSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
variable {α : Type}

theorem native_safe (entry : RemoteMap) (h : List RemoteDriver.Event) (g : WGWorld)
    (hi : NativeInv entry h g) : RemoteDriver.Safe h := hi.2

theorem access_retained (entry : RemoteMap) (observed : MixedM α) (action : WG.M α)
    (erases : ErasesStatePrefix observed action)
    (keep : ∀ before, Ensures action (RemoteSilent.Retained before)
      (fun _ => RemoteSilent.Retained before)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) RemoteDriver.Safe
      (RemoteConfiguration.access RemoteDriver.Event.rx RemoteDriver.rxEvent observed) := by
  intro g
  exact focused_retained_inert effect entry RemoteDriver.EventValid
    RemoteDriver.Event.rx RemoteDriver.rxEvent (fun _ => True.intro)
    (fun _ => destinationAt g) (fun (out : α × WGWorld) (_ : Ambient) => destinationAt out.2)
    ((RoutingJoint.nativeRx observed).run g) (action.run g)
    (nativeRx_inert observed g)
    ((StateAppends.focus _ _ _) g)
    ((focusStatePrefix_erases _ _
      (focusStatePrefix_erases _ _ erases)) g)
    (fun a out b run => keep (destinationAt g) g a out.1 out.2 b (.refl _) run)

theorem native_lift_retained (entry : RemoteMap) (action : WG.M α)
    (keep : ∀ before, Ensures action (RemoteSilent.Retained before)
      (fun _ => RemoteSilent.Retained before)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) RemoteDriver.Safe
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h g a hi; exact hi.2
  · intro h g a value final b hi run
    exact ⟨last_iff_replay.mpr ((last_to_replay hi.1).trans
      (keep (destinationAt g) g a value final b (.refl _) run)),hi.2⟩

theorem configuration_contracts (entry : RemoteMap) :
    RemoteConfiguration.Invariant.Contracts (NativeInv entry) :=
  ⟨native_safe entry,native_lift_retained entry,access_retained entry,
    endpoint_preserves entry,birth_preserves entry⟩

theorem configuration_preserves (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) RemoteDriver.Safe
      (RemoteConfiguration.setDevice RemoteDriver.Event.rx RemoteDriver.rxEvent
        RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) :=
  RemoteConfiguration.Invariant.setDevice_preserves (configuration_contracts entry) attrs

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
