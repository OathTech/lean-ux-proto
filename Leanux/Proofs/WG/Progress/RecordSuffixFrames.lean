import Leanux.Proofs.Framing.Product
/-! Lift an actual Ambient contract through the original product-state adapter. Unlike store-only frames, this retains a predicate on Ambient itself. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing

theorem liftAmbient_contract {α : Type} (action : AmbientM α)
    (P : Ambient → Prop) (Q : α → Ambient → Prop) (spec : Hoare action P Q) :
    Hoare (liftAmbient action) (fun w => P w.ambient) (fun value w => Q value w.ambient) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  rw [liftAmbient_run] at run
  cases inner : action.run before.ambient with
  | error error => simp only [inner,Except.map] at run; cases run
  | ok pair =>
    obtain ⟨result,ambient⟩ := pair
    simp only [inner,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact (hoare_iff_run _ _ _).mp spec before.ambient result ambient pre inner
end Leanux.Proofs.WG.Progress.RecordSuffix
