import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPrepareReadSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessFrames

/-! Getter interiors preserve the packet account. The packet-store adapter
uses its actual returned-store equation at the write-back boundary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem readRx_frame (id : SkbId) : SameView StagedEntry.view (getRxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  exact congrArg StagedEntry.view (Packets.getRxSkb_current _ _ _ _ _ _ performed).1

theorem ReadPoint.frame {E α : Type} {body : WGPrefix E α} {token : Access body}
    (point : ReadPoint token w a v b) : StagedEntry.view v = StagedEntry.view w := by
  cases point with
  | peer point => exact congrArg StagedEntry.view point.world
  | key point => exact congrArg StagedEntry.view point.world
  | rx point => exact point.frame (readRx_frame _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
