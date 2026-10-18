import Leanux.Proofs.WG.Noise.DriverTagLeafFrames
import Leanux.Proofs.WG.Noise.PendingSchedulerFrames

/-! The product boundary projects only the WireGuard tag map. Existing typed
subsystem/store frames supply every unrelated-state fact. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

abbrev ProductObs := PrefixM DriverTagEvent

def StateInv (entry : TagMap) (h : List DriverTagEvent) (w : World) : Prop :=
  NativeInv entry h w.wg

theorem safe (entry : TagMap) (h : List DriverTagEvent) (w : World)
    (prior : StateInv entry h w) : ValidHistory h := prior.2

theorem state_tags (entry : TagMap) (h : List DriverTagEvent) (w v : World)
    (same : tagView v.wg = tagView w.wg) (prior : StateInv entry h w) :
    StateInv entry h v := by
  exact ⟨by change DriverTagMapCoverage entry h (tagView v.wg); rw [same]; exact prior.1,
    prior.2⟩

theorem state_store (entry : TagMap) (h : List DriverTagEvent) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (prior : StateInv entry h w) :
    StateInv entry h v :=
  state_tags entry h w v (congrArg (fun s : WGStoreView => responseTagMap s.dev) same) prior

theorem state_product_store (entry : TagMap) (h : List DriverTagEvent) (w v : World)
    (same : productStoreView v = productStoreView w) (prior : StateInv entry h w) :
    StateInv entry h v :=
  state_store entry h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same) prior

theorem lift_product_frame {α : Type} (entry : TagMap) (action : Leanux.M α)
    (frame : SameView (fun w : World => tagView w.wg) action) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix action) :=
  viewLiftPrefix_preserves _ (safe entry) (state_tags entry) frame

theorem lift_product_store {α : Type} (entry : TagMap) (action : Leanux.M α)
    (frame : SameProductStore action) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix action) :=
  viewLiftPrefix_preserves _ (safe entry) (state_product_store entry) frame

theorem native_product_frame {α : Type} (action : WG.M α)
    (frame : SameView tagView action) :
    SameView (fun w : World => tagView w.wg) (liftWG action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value final original
  rw [liftWG_run] at original
  cases run : (action.run w.wg).run w.ambient with
  | error stop => simp [run,Except.map] at original
  | ok result =>
    rcases result with ⟨⟨value,g⟩,after⟩
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at original
    obtain ⟨rfl,rfl⟩ := original
    exact (ProjectedAction.iff_run_ambient _ _ _).mp frame
      w.wg w.ambient value g after run

theorem native_product_retained {α : Type} (action : WG.M α)
    (frame : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      TagsRetained (tagView g) (tagView final))
    (w : World) (value : α) (final : World)
    (original : (liftWG action).run w = .ok (value,final)) :
    TagsRetained (tagView w.wg) (tagView final.wg) := by
  rw [liftWG_run] at original
  cases run : (action.run w.wg).run w.ambient with
  | error stop => simp [run,Except.map] at original
  | ok result =>
    rcases result with ⟨⟨value,g⟩,after⟩
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at original
    obtain ⟨rfl,rfl⟩ := original
    exact frame w.wg w.ambient value g after run

end Leanux.Proofs.WG.Noise.DriverTags

