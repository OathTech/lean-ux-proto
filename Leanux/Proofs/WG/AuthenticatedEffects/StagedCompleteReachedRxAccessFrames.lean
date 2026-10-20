import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessFrames

/-! RX reads and updates preserve the complete TX projection at each adapter and source-tree point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.frame (source : Shape action) : SameView StagedEntry.view action := by
  induction source with
  | access source=>exact source.frame
  | skb action frame=>exact frame
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.frame (point : Point source w a v b) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry source=>rfl
  | returned source performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | access point=>exact point.frame
  | skb frame point=>exact point.frame frame
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
