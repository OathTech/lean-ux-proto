import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierModel
import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierFrames
import Leanux.Proofs.WG.Keypairs.Frames.EnvWorkers
import Leanux.Proofs.WG.Keypairs.Frames.Env

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
abbrev CounterMono {α : Type} (action : WG.M α) : Prop :=
  ∀g ambient value final after,((action.run g).run ambient)=.ok ((value,final),after) →
    g.keypairCounter≤final.keypairCounter
abbrev ProductCounterMono {α : Type} (action : Leanux.M α) : Prop :=
  ∀w value final,action.run w=.ok (value,final) → w.wg.keypairCounter≤final.wg.keypairCounter
theorem ordinary_counter {α : Type} {action : WG.M α}
    (ordinary : Keypairs.OrdinaryAction action) : CounterMono action := by
  intro g a value final after run
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp ordinary g a value final after run).frontier_mono
theorem product_ordinary_counter {α : Type} {action : Leanux.M α}
    (ordinary : Keypairs.ProductOrdinaryAction action) : ProductCounterMono action := by
  intro w value final run
  exact ((ProjectedAction.iff_run _ _ _).mp ordinary w value final run).frontier_mono
theorem product_snapshot_counter {α : Type} {action : Leanux.M α}
    (same : SameView (fun w : World=>Keypairs.snapshot w.wg) action) : ProductCounterMono action :=
  product_ordinary_counter (Keypairs.SameView.ordinary same)
theorem counter_product {α : Type} {action : WG.M α} (mono : CounterMono action) :
    ProductCounterMono (liftWG action) := by
  intro w value final run
  rw [liftWG_run] at run
  cases actual : (action.run w.wg).run w.ambient with
  | error stop => simp [actual,Except.map] at run
  | ok out =>
    obtain ⟨⟨x,g⟩,a⟩:=out
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩:=run
    exact mono w.wg w.ambient x g a actual
theorem frontier_store (h : List Event) (w v : World)
    (same : productStoreView v=productStoreView w) (prior : Frontier h w.wg.keypairCounter) :
    Frontier h v.wg.keypairCounter := by
  have eq := congrArg (fun p : ProductStore43=>p.2.2.2.keypairCounter) same
  change v.wg.keypairCounter=w.wg.keypairCounter at eq
  simpa only [eq] using prior

theorem frontier_wg_store (h : List Event) (g v : WGWorld)
    (same : wgStoreView v=wgStoreView g) (prior : Frontier h g.keypairCounter) :
    Frontier h v.keypairCounter := by
  have eq := congrArg (fun p : WGStoreView=>p.keypairCounter) same
  change v.keypairCounter=g.keypairCounter at eq
  simpa only [eq] using prior
theorem counter_native_frame {α : Type} {action : WG.M α} (same : CounterSame action) :
    SameView (fun w : World=>w.wg.keypairCounter) (liftWG action) := by
  apply sameView_liftWG (fun w : World=>w.wg.keypairCounter) WGWorld.keypairCounter action
    ((ProjectedAction.iff_run_ambient _ _ _).mpr same)
  intro w g a eq
  exact eq
theorem counter_product_frame {α : Type} {action : Leanux.M α}
    (same : SameView (fun w : World=>w.wg.keypairCounter) action) : ProductCounterMono action := by
  intro w value final run
  exact Nat.le_of_eq (((ProjectedAction.iff_run _ _ _).mp same w value final run).symm)
end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
