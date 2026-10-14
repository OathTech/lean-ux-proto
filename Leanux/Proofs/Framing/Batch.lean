import Leanux.Proofs.Framing.KernelEffects
import Leanux.Env.Batch
import Leanux.Proofs.Framing.Projection

/-! Full-kernel frames for read-only and record-only scheduler leaves. These frames alone
make no internal-access claim; the lifetime observers inspect their source. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

/-- A callback frame lifts through section records and NET_RX scalar metadata. -/
theorem runWorker_sameView {σ : Type} (view : World → σ)
    (hv : ∀ w v, v.k = w.k → view v = view w) (worker : Worker) (body : M Unit)
    (hb : SameView view body) : SameView view (Env.runWorker worker body) := by
  unfold Env.runWorker
  repeat' first
    | exact hb
    | exact (fun w x v hr => hv w v (hidden_sameKernel _ w x v hr))
    | exact (fun w x v hr => hv w v (by cases hr; rfl))
    | exact SameView.pure view _
    | apply SameView.bind
    | split
    | (intro x; try dsimp only)

theorem runWorker_sameKernel (worker : Worker) (body : M Unit) (hb : SameKernel body) :
    SameKernel (Env.runWorker worker body) :=
  runWorker_sameView (·.k) (fun _ _ he => he) worker body hb

theorem condResched_sameKernel (self : Worker) : SameKernel (Env.condResched self) := by
  apply sameKernel_of_wp
  intro k
  have hp := sameKernel_wp _ peekHiddenSite_sameKernel (fun s => s = k)
  have hh := fun site => sameKernel_wp _ (hidden_sameKernel site) (fun s => s = k)
  mvcgen [Env.condResched, hp, hh, invariant]

/-- The trial's returned World is discarded on every outcome. This endpoint
frame is separate from a proof of accesses made inside the trial. -/
theorem activationConsistent_sameKernel (a : Activation) : SameKernel (Env.Activation.consistent a) := by
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

theorem filterAuxM_sameKernel (f : α → M Bool) (hf : ∀ a, SameKernel (f a))
    (xs acc : List α) : SameKernel (List.filterAuxM f xs acc) := by
  induction xs generalizing acc with
  | nil => exact sameKernel_pure _
  | cons a xs ih => exact sameKernel_bind (hf a) (fun b => ih (cond b (a :: acc) acc))

theorem filterM_sameKernel (f : α → M Bool) (hf : ∀ a, SameKernel (f a))
    (xs : List α) : SameKernel (xs.filterM f) :=
  sameKernel_bind (filterAuxM_sameKernel f hf xs []) (fun ys => sameKernel_pure ys.reverse)

theorem activationOccupancy_sameKernel (a : Activation) : SameKernel (Env.Activation.occupancy a) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.Activation.occupancy, getDev, getK, getPeer, invariant]

theorem activationHasWork_sameKernel (a : Activation) : SameKernel (Env.Activation.hasWork a) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.Activation.hasWork, getDev, getK, getPeer, getTxSkb, invariant]

end Leanux.Proofs.Framing
