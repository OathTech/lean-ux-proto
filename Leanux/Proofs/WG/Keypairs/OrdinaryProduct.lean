import Leanux.Proofs.WG.Keypairs.Ordinary
import Leanux.Proofs.Framing.Lift

/-! Ordinary evolution over the actual runner product. Native WG actions
enter this contract only through the mirror's real lift. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.Proofs.Framing

abbrev ProductOrdinaryAction (a : Leanux.M α) : Prop :=
  Lifetimes.ProjectedAction (fun w : World => snapshot w.wg) Ordinary a

theorem OrdinaryAction.liftWG {a : WG.M α} (h : OrdinaryAction a) :
    ProductOrdinaryAction (Leanux.liftWG a) := by
  apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp h _ _ _ _ _ he

end Leanux.Proofs.WG.Keypairs
