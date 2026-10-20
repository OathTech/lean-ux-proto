import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessSource

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.frame (source : Shape action) : SameView (fun w : WGWorld=>w) action := by
  induction source with
  | pure value=>exact SameView.pure _ _
  | read=>
      intro initial
      exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2)
  | ambient action=>exact fun _=>hoare_liftAmbient action _
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.world (point : Point source w a v b) : v=w := by
  induction point with
  | entry source=>rfl
  | returned source performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadAccess
