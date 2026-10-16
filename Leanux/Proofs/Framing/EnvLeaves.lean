import Leanux.Env
import Leanux.Proofs.Framing.Product

/-! Frames over the original 43-field product observation for environment
bookkeeping. These make no source-access claim and retain the actual Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem deliverSent_sameKernel : SameProductStore Env.deliverSent := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  have hm := productModifyWG_spec (fun s => s = k)
  have hl (α β : Type) := list_view_spec (m := Except Stop) productStoreView
    (α := α) (β := β) (fun s => s = k)
  unfold Hoare at ha hg hr hm
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    Env.deliverSent, getRouting, hg, hr, hm, ha, hl, modifyEnv, unsupported]
  all_goals simp_all [productStoreView, wgStoreView]

theorem peekNextSite_sameKernel : SameProductStore Env.peekNextSite := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.peekNextSite, getAmbient, ha]

theorem requireNoCryptWork_sameKernel : SameProductStore Env.requireNoCryptWork := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  unfold Hoare at ha hg
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.requireNoCryptWork, hg, ha, unsupported]

theorem timerWorker_sameKernel (t : PeerTimer) : SameProductStore (Env.timerWorker t) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.timerWorker, ha, invariant]

theorem advance_sameKernel (ticks : Nat) : SameProductStore (Env.advance ticks) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  have hm := productModifyWG_spec (fun s => s = k)
  unfold Hoare at ha hg hm
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.advance, getAmbient, hidden,
    hg, hm, ha, modifyEnv, unsupported]
  all_goals simp_all [productStoreView, wgStoreView]

end Leanux.Proofs.Framing
