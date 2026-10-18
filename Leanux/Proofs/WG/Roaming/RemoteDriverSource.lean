import Leanux.Proofs.WG.Roaming.RemoteDriverBridge
import Leanux.Proofs.WG.Roaming.RemoteConfigurationAppendSource
import Leanux.Proofs.WG.Roaming.RemoteWorkerSource
import Leanux.Proofs.WG.Roaming.RemoteMaintenanceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
variable {α : Type}

theorem safe (entry : RemoteMap) (h : List Event) (w : World) (pre : Inv entry h w) : Safe h := pre.2

theorem native_safe (entry : RemoteMap) (h : List Event) (g : WGWorld)
    (pre : NativeInv entry h g) : Safe h := pre.2

theorem focus_retained (entry : RemoteMap) (observed : RxHistory.Obs α) (action : Leanux.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (retained : ∀ before, Preserves (fun w : World => RemoteSilent.Retained before w.wg) action) :
    PrefixPreserves (Inv entry) Safe (focus observed) := by
  apply RemoteOrigin.focused_retained entry Cause EventValid Event.rx rxEvent (fun _ => True.intro)
    (fun w : World => destinationAt w.wg) (fun (_ : α) w => destinationAt w.wg)
    observed action appends erases
  intro w value final run
  exact (hoare_iff_run _ _ _).mp (retained (destinationAt w.wg)) w value final
    (RemoteRetained.refl _) run

theorem focus_store (entry : RemoteMap) (observed : RxHistory.Obs α) (action : Leanux.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (stored : SameProductStore action) : PrefixPreserves (Inv entry) Safe (focus observed) :=
  focus_retained entry observed action appends erases
    (fun before => RemoteWorkers.product_store before action stored)

theorem focus_native (entry : RemoteMap) (observed : RxHistory.Obs α) (action : WG.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed (liftWG action))
    (retained : ∀ before, Ensures action (RemoteSilent.Retained before)
      (fun _ => RemoteSilent.Retained before)) :
    PrefixPreserves (Inv entry) Safe (focus observed) :=
  focus_retained entry observed (liftWG action) appends erases
    (fun before => PublicationPoll.native_product (RemoteSilent.Retained before) action
      ((ensures_iff _ _ _).mp (retained before)))

theorem access_retained (entry : RemoteMap) (observed : MixedM α) (action : WG.M α)
    (erases : ErasesStatePrefix observed action)
    (retained : ∀ before, Ensures action (RemoteSilent.Retained before)
      (fun _ => RemoteSilent.Retained before)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) Safe
      (RemoteConfiguration.access Event.rx rxEvent observed) := by
  apply RemoteOrigin.native_focused_retained entry Cause EventValid Event.rx rxEvent
    (fun _ => True.intro) destinationAt (RoutingJoint.nativeRx observed) action
    (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _ erases))
  intro g a value final b run
  exact retained (destinationAt g) g a value final b (RemoteRetained.refl _) run

theorem native_lift_retained (entry : RemoteMap) (action : WG.M α)
    (retained : ∀ before, Ensures action (RemoteSilent.Retained before)
      (fun _ => RemoteSilent.Retained before)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h g a pre; exact pre.2
  · intro h g a value final b pre run
    exact ⟨pre.1.retained (retained (destinationAt g) g a value final b
      (RemoteRetained.refl _) run),pre.2⟩

end Leanux.Proofs.WG.Roaming.RemoteDriver
