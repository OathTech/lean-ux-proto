import Leanux.Proofs.Framing.Product
import Leanux.Syscalls

/-! Closing fixture holders composes actual filesystem actions at the runner
boundary. Namespace cleanup still occurs in the enclosing environment step. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

namespace SyscallFrames
theorem netnsClose_sameWGStore :
    SameView (fun w : World => wgStoreView w.wg) netnsClose := by
  apply SameView.of_wp
  intro initial
  have fsSpec {α : Type} (a : FS.M α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => wgStoreView w.wg = initial) (fun _ w => wgStoreView w.wg = initial) :=
    productFS_spec a _ (fun _ _ _ _ h => h)
  have ambientSpec {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => wgStoreView w.wg = initial) (fun _ w => wgStoreView w.wg = initial) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have routeSpec :
      Hoare (getRouting : Leanux.M Net.Routing)
        (fun w => wgStoreView w.wg = initial) (fun _ w => wgStoreView w.wg = initial) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x w' hp hr
    cases hr
    exact hp
  unfold Hoare at fsSpec ambientSpec routeSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, netnsClose, routeSpec, getEnv, fsSpec,
    unsupported, invariant, ambientSpec]
  all_goals try exact (⇓? _ w => ⌜wgStoreView w.wg = initial⌝)
  all_goals simp_all

theorem netnsClose_spec (P : WGStoreView → Prop) :
    ⦃fun w : World => ⌜P (wgStoreView w.wg)⌝⦄ netnsClose
    ⦃⇓? _ w => ⌜P (wgStoreView w.wg)⌝⦄ := netnsClose_sameWGStore.wp P

end SyscallFrames
end Leanux.Proofs.Framing
