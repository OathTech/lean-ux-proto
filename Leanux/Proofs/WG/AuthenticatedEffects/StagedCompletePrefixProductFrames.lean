import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProduct

/-! Actual store frames transport the complete carrier and leave the retained
prefix certificate unchanged. No event-producing actor uses these rules. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem carrier_safe (h : List Event) (w : World) (before : ProductCarrier h w) :
    All CompleteProduct.Safe h := before.2

theorem stable (h : List Event) (w v : World)
    (same : productStoreView v=productStoreView w) (before : ProductCarrier h w) :
    ProductCarrier h v := ⟨CompleteProduct.stable h w v same before.1,before.2⟩

theorem store_transport (h : List Event) (w v : World)
    (same : wgStoreView v.wg=wgStoreView w.wg) (before : ProductCarrier h w) :
    ProductCarrier h v := ⟨CompleteProduct.store_transport h w v same before.1,before.2⟩

theorem store (action : Leanux.M α) (frame : SameView (fun w : World=>wgStoreView w.wg) action) :
    Checked (liftPrefix action) := native action (CompleteProduct.store action frame)

theorem product_store (action : Leanux.M α) (frame : SameProductStore action) :
    Checked (liftPrefix action) := native action (CompleteProduct.product_store action frame)

theorem ambient (action : AmbientM α) : Checked (liftPrefix (monadLift action : Leanux.M α)) :=
  native _ (CompleteProduct.ambient action)

theorem fs (action : FS.M α) : Checked (liftPrefix (liftFS action)) := native _ (CompleteProduct.fs action)

theorem task (action : TaskM α) : Checked (liftPrefix (liftTask action)) := native _ (CompleteProduct.task action)

theorem seccomp (action : Seccomp.M α) : Checked (liftPrefix (liftSeccomp action)) :=
  native _ (CompleteProduct.seccomp action)

theorem routing (action : Net.M α) : Checked (liftPrefix (monadLift action : Leanux.M α)) :=
  native _ (CompleteProduct.routing action)

theorem read : Checked (liftPrefix (get : Leanux.M World)) := native _ CompleteProduct.read

theorem edit (f : World→World) (same : ∀ w, wgStoreView (f w).wg=wgStoreView w.wg) :
    Checked (liftPrefix (_root_.modify f : Leanux.M Unit)) := native _ (CompleteProduct.edit f same)

theorem env_edit (f : EnvWorld→EnvWorld) : Checked (liftPrefix (modifyEnv f)) :=
  native _ (CompleteProduct.env_edit f)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
