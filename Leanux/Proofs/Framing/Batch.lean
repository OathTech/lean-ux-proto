import Leanux.Env.Batch
import Leanux.Proofs.Framing.Product
import Leanux.Proofs.WG.Packets.Primitives

/-! Product frames over the original 43 store observations. Arbitrary worker
and filter callbacks retain their scope. These frames make no access claim. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

/-- A callback frame lifts through actual section records and NET_RX metadata. -/
theorem runWorker_sameView {σ : Type} (view : World → σ)
    (hv : ∀ w v, productStoreView v = productStoreView w → view v = view w)
    (worker : Worker) (body : Leanux.M Unit)
    (hb : SameView view body) : SameView view (Env.runWorker worker body) := by
  apply SameView.of_wp
  intro initial
  have hb' := hb.wp (fun v => v = initial)
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => view w = initial)
    (fun w ambient hp => (hv w {w with ambient} rfl).trans hp)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.runWorker, hidden, modifyAmbient, ha, hb']

theorem condResched_sameKernel (self : Worker) : SameProductStore (Env.condResched self) := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = initial) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.condResched, peekHiddenSite, hidden, invariant, ha]

/-- The actual trial runs on a copied product World. Its state is discarded;
hidden mismatches return false and every other Stop propagates. -/
theorem activationConsistent_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.consistent a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w b v hr
  unfold Env.Activation.consistent at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases he : (Env.Activation.run a).run w with
  | ok out =>
    simp only [he, StateT.run_pure] at hr
    cases hr
    rfl
  | error e =>
    simp only [he, StateT.run_pure] at hr
    cases e <;> cases hr <;> rfl

theorem filterAuxM_sameKernel {S σ α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (view : S → σ)
    (f : α → StateT S m Bool) (hf : ∀ a, SameView view (f a))
    (xs acc : List α) : SameView view (List.filterAuxM f xs acc) := by
  induction xs generalizing acc with
  | nil => exact SameView.pure view _
  | cons a xs ih => exact SameView.bind (hf a) (fun b => ih (cond b (a :: acc) acc))

theorem filterM_sameKernel {S σ α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (view : S → σ)
    (f : α → StateT S m Bool) (hf : ∀ a, SameView view (f a))
    (xs : List α) : SameView view (xs.filterM f) :=
  SameView.bind (filterAuxM_sameKernel view f hf xs []) (fun ys => SameView.pure view ys.reverse)

theorem activationOccupancy_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.occupancy a) := by
  have dev : SameWGStore WG.getDev := by
    intro initial
    unfold Hoare
    mvcgen [WG.getDev, invariant, AmbientM.invariant]
  have peer (pid : PeerId) : SameWGStore (getPeer pid) := by
    intro initial
    unfold Hoare
    mvcgen [getPeer, WG.getDev, invariant, AmbientM.invariant]
  apply SameView.of_wp
  intro initial
  have hd := (liftWG_sameProductStore WG.getDev dev).wp (fun s => s = initial)
  have hp := fun pid => (liftWG_sameProductStore (getPeer pid) (peer pid)).wp (fun s => s = initial)
  have ha := fun α (x : AmbientM α) => productAmbient_spec x
    (fun w => productStoreView w = initial) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.Activation.occupancy, hd, hp, invariant, ha]

theorem activationHasWork_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.hasWork a) := by
  have dev : SameWGStore WG.getDev := by
    intro initial
    unfold Hoare
    mvcgen [WG.getDev, invariant, AmbientM.invariant]
  have peer (pid : PeerId) : SameWGStore (getPeer pid) := by
    intro initial
    unfold Hoare
    mvcgen [getPeer, WG.getDev, invariant, AmbientM.invariant]
  have packet (id : SkbId) : SameWGStore (getTxSkb id) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient p g' ambient' hr
    rw [(Leanux.Proofs.WG.Packets.getTxSkb_current id g g' p ambient ambient' hr).1]
  apply SameView.of_wp
  intro initial
  have hd := (liftWG_sameProductStore WG.getDev dev).wp (fun s => s = initial)
  have hp := fun pid => (liftWG_sameProductStore (getPeer pid) (peer pid)).wp (fun s => s = initial)
  have ht := fun id => (liftWG_sameProductStore (getTxSkb id) (packet id)).wp (fun s => s = initial)
  have ha := fun α (x : AmbientM α) => productAmbient_spec x
    (fun w => productStoreView w = initial) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.Activation.hasWork, hd, hp, ht, invariant, ha]

end Leanux.Proofs.Framing
