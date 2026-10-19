import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Keypairs.Frames.Tools
import Leanux.Proofs.WG.Keypairs.OrdinaryProduct
/-! Physical store projections and normal counter monotonicity lifting. These rules preserve the supplied history safety predicate on every source outcome; mutable callbacks are handled separately. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookState
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Keypairs
variable {E α : Type} {I : List E → World → Prop} {S : List E → Prop}
def StoreTransport (I : List E → World → Prop) : Prop :=
  ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v
theorem product_transport (transport : StoreTransport I) :
    ∀ h w v, productStoreView v = productStoreView w → I h w → I h v :=
  fun h w v same => transport h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same)
theorem lift_store (safe : ∀ h w, I h w → S h) (transport : StoreTransport I)
    (action : Leanux.M α) (frame : SameProductStore action) :
    PrefixPreserves I S (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView safe (product_transport transport) frame
theorem ambient (safe : ∀ h w, I h w → S h) (transport : StoreTransport I)
    (action : AmbientM α) :
    PrefixPreserves I S (liftPrefix (monadLift action : Leanux.M α)) :=
  lift_store safe transport _ (fun _ => productAmbient_spec action _ (fun _ _ h => h))
theorem store_snapshot {α : Type} (action : Leanux.M α) (frame : SameProductStore action) :
    SameView (fun w : World => snapshot w.wg) action :=
  frame.of_factor (fun s : ProductStore43 => snapshotOfWGStoreView s.2.2.2)
    (fun w : World => snapshot w.wg) (fun _ => rfl)

/-- A sufficient condition for the counter-only frontier invariant. Arbitrary
state invariants may instead supply the explicit mutable StateLeaves. -/
def CounterTransport (I : List E → World → Prop) : Prop :=
  ∀ h w v, w.wg.keypairCounter ≤ v.wg.keypairCounter → I h w → I h v
theorem counter_store (transport : CounterTransport I) : StoreTransport I := by
  intro h w v same pre
  apply transport h w v _ pre
  exact Nat.le_of_eq (congrArg WGStoreView.keypairCounter same).symm
theorem ordinary_lift (safe : ∀ h w, I h w → S h) (transport : CounterTransport I)
    {α : Type} (action : Leanux.M α) (ordinary : ProductOrdinaryAction action) :
    PrefixPreserves I S (liftPrefix action) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift action safe
  intro h w x v pre run
  exact transport h w v
    ((ProjectedAction.iff_run _ _ _).mp ordinary w x v run).frontier_mono pre
end Leanux.Proofs.WG.TimerDiscipline.HookState
