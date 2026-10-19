import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryContracts
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Stateful source-composition contracts for the original delivery callers.
Delivery is an explicit obligation: store frames cannot justify a carrier that
also describes the sent queue being cleared. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint.PollSource
variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

theorem afterBatch_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (crypt send sendOne : PrefixM E Unit) (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit) (deliver : PrefixM E Unit)
    (hc : PrefixPreserves I S crypt) (hs : PrefixPreserves I S send) (ho : PrefixPreserves I S sendOne)
    (hsch : ∀ stack, PrefixPreserves I S (schedule stack))
    (hd : ∀ what flags, PrefixPreserves I S (drained what flags))
    (hdeliver : PrefixPreserves I S deliver) :
    PrefixPreserves I S (afterBatchWith crypt send sendOne schedule drained deliver) := by
  unfold afterBatchWith
  repeat' first
    | (poll_preserve_head crypt; exact hc)
    | (poll_preserve_head send; exact hs)
    | (poll_preserve_head sendOne; exact ho)
    | (poll_preserve_head schedule; exact hsch _)
    | (poll_preserve_head drained; exact hd _ _)
    | (poll_preserve_head deliver; exact hdeliver)
    | traffic_preserve_source safe using store

theorem observeFront_store : SameProductStore observeFront := by
  have ambient {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have wg : SameProductStore getWG := fun k => productGetWG_spec (fun s => s = k)
  have crypt := requireNoCryptWork_sameKernel
  env_operation_source [observeFront,unsupported] using [wg,crypt,ambient]

theorem observeFinish_store : SameProductStore observeFinish := by
  have wg : SameProductStore getWG := fun k => productGetWG_spec (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    fun k => productRouting_spec ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
      (fun s => s = k)
  have fixture : SameProductStore getEnv := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  have editFixture (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  env_operation_source [observeFinish] using [wg,routing,fixture,editFixture]

theorem observe_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (deliver : PrefixM E Unit) (hdeliver : PrefixPreserves I S deliver) :
    PrefixPreserves I S (observeWith deliver) :=
  PrefixPreserves.bind (viewLiftPrefix_preserves productStoreView safe store observeFront_store) (fun _ =>
    PrefixPreserves.bind hdeliver (fun _ =>
      viewLiftPrefix_preserves productStoreView safe store observeFinish_store))

/-- Recording the pre-delivery projection preserves a supplied invariant
only when the new event and the actual native delivery both preserve it. -/
theorem observed_preserves (record : List SentDatagram → E)
    (safe : ∀ h w, I h w → S h)
    (append : ∀ h w sent, I h w → I (h ++ [record sent]) w)
    (native : PrefixPreserves I S (liftPrefix deliverSent)) :
    PrefixPreserves I S (observed record) := by
  have read : PrefixPreserves I S (liftPrefix getWG) :=
    PrefixEnsures.lift (P := I) (S := S) (Q := fun _ h w => I h w) getWG safe
      (fun _ _ _ _ hi run => by cases run; exact hi)
  unfold observed
  apply PrefixPreserves.bind read
  intro w
  have emit : PrefixPreserves I S (emitPrefix (record w.sent)) := by
    intro v h hi
    have next := append h v w.sent hi
    exact ⟨[record w.sent],rfl,safe _ _ next,next⟩
  exact PrefixPreserves.bind emit (fun _ => native)

end Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
