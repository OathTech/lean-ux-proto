import Leanux.Proofs.WG.Index.ReachedProjectionFrames
import Leanux.Proofs.WG.Index.ReachedRunnerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedTraffic
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem any_safe (loans : Reservations) (h : List RxHistory.Event) (w : World)
    (pre : Reached.AnyAux loans h w) : OwnerChecks.Safe h := by
  obtain ⟨_,pre⟩ := pre
  exact pre.1.2.1.safe

theorem any_product_store (loans : Reservations) (h : List RxHistory.Event) (w v : World)
    (same : productStoreView v=productStoreView w)
    (pre : Reached.AnyAux loans h w) : Reached.AnyAux loans h v := by
  obtain ⟨cs,pre⟩ := pre
  exact ⟨cs,Reached.aux_store same pre⟩

theorem any_wg_store (loans : Reservations) (h : List RxHistory.Event) (w v : World)
    (same : wgStoreView v.wg=wgStoreView w.wg)
    (pre : Reached.AnyAux loans h w) : Reached.AnyAux loans h v := by
  obtain ⟨cs,pre⟩ := pre
  have kept : Reached.Aux cs loans h h {w with wg:=v.wg} :=
    Reached.aux_store (by simp only [productStoreView,same]) pre
  exact ⟨cs,Reached.aux_wg_equal (w:={w with wg:=v.wg}) (v:=v) rfl kept⟩

theorem entry_lift {α : Type} (action : Leanux.M α)
    (same : SameView (fun w : World=>wgStoreView w.wg) action) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (liftPrefix action) :=
  viewLiftPrefix_preserves (fun w : World=>wgStoreView w.wg)
    Reached.anyEntry_safe Reached.anyEntry_store same

end Leanux.Proofs.WG.Index.ReachedTraffic
