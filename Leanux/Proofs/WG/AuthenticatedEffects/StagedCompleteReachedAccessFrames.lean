import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessSource

/-! Every actual point, including before a later failure, preserves the
complete ticket projection because each individual world write does. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Access
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.frame (source : Shape action) : SameView StagedEntry.view action := by
  induction source with
  | pure value=>exact SameView.pure _ _
  | read=>
      intro initial
      exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2)
  | ambient action=>exact fun _=>hoare_liftAmbient action _
  | write update frame=>exact frame
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.frame (point : Point source w a v b) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry source=>rfl
  | returned source performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Access
