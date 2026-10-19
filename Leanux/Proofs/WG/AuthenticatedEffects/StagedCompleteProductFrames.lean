import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct
import Leanux.Proofs.Framing.Product

/-! Native product frames are stated on actual WG-store projections. They
retain the same historical ledger and the allocation invariant independently
of ambient, file, task and routing state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem store_transport (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (before : Carrier h w) : Carrier h v := by
  obtain ⟨⟨ledger,accounted⟩,old,allocated⟩ := before
  have view : StagedEntry.view v.wg = StagedEntry.view w.wg :=
    congrArg (fun s : WGStoreView => StagedEntry.view {dev := s.dev}) same
  exact ⟨⟨ledger,accounted.same_view view⟩,old,allocated.store same⟩

theorem stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (before : Carrier h w) : Carrier h v :=
  store_transport h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same) before

theorem store (action : Leanux.M α) (frame : SameView (fun w : World => wgStoreView w.wg) action) :
    Checked (liftPrefix action) :=
  native action (fun h => (hoare_iff_run _ _ _).mpr (fun w value v before run =>
    store_transport h w v ((ProjectedAction.iff_run _ _ _).mp frame w value v run) before))

theorem product_store (action : Leanux.M α) (frame : SameProductStore action) :
    Checked (liftPrefix action) :=
  store action (frame.of_factor (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl))

theorem ambient (action : AmbientM α) : Checked (liftPrefix (monadLift action : Leanux.M α)) :=
  native _ (fun _ => productAmbient_spec action _ (fun _ _ before => before))

theorem fs (action : FS.M α) : Checked (liftPrefix (liftFS action)) :=
  native _ (fun _ => productFS_spec action _ (fun _ _ _ _ before => before))

theorem task (action : TaskM α) : Checked (liftPrefix (liftTask action)) :=
  native _ (fun _ => productTask_spec action _ (fun _ _ _ before => before))

theorem seccomp (action : Seccomp.M α) : Checked (liftPrefix (liftSeccomp action)) :=
  native _ (fun _ => productSeccomp_spec action _ (fun _ _ _ _ before => before))

theorem routing (action : Net.M α) : Checked (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (· = initial))

theorem read : Checked (liftPrefix (get : Leanux.M World)) :=
  native _ (fun _ => hoare_consequence (hoare_get _) (fun _ before => before) (fun _ _ before => before.2))

theorem edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    Checked (liftPrefix (_root_.modify f : Leanux.M Unit)) :=
  native _ (fun h => hoare_modify _ (fun w before => store_transport h w (f w) (same w) before))

theorem env_edit (f : EnvWorld → EnvWorld) : Checked (liftPrefix (modifyEnv f)) := by
  apply store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
