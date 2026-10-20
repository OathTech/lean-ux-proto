import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductStoreSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductFrames

/-! Store frames transport the same packet ledger and allocation companion
through each actual source point, independently of Ambient state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

theorem Shape.frame (source : Shape action) : SameView (fun w : World=>wgStoreView w.wg) action := by
  induction source with
  | pure value => exact SameView.pure _ _
  | reading source => exact source.frame.factor wgStoreView
  | ambient body => exact fun _ => productAmbient_spec body _ (fun _ _ h=>h)
  | write update same => exact fun _ => hoare_modify update (fun w before=>(same w).trans before)
  | bind head tail ihHead ihTail => exact SameView.bind ihHead ihTail

theorem Point.store (point : Point source w v) : wgStoreView v.wg=wgStoreView w.wg := by
  induction point with
  | entry source => rfl
  | returned source performed => exact (ProjectedAction.iff_run _ _ _).mp source.frame _ _ _ performed
  | reading point => exact congrArg wgStoreView point.world
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      exact ih.trans ((ProjectedAction.iff_run _ _ _).mp head.frame _ _ _ leading)

theorem Point.carrier (point : Point source w v) (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h v := CompleteProduct.store_transport h w v point.store before

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked (liftPrefix action) :=
  CompleteProduct.store action source.frame

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
