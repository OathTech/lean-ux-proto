import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeFrames

/-! Every metadata write preserves the allocation identity and TX queues of the peer read by the same source prefix. Frames and source equations remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.frame (source : Shape action) : SameView StagedEntry.view action := by
  induction source with
  | access source=>exact source.frame
  | update pid f next same tail ih=>exact HandshakeFrames.update_then pid f next same ih
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.frame (point : Point source w a v b) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry source=>rfl
  | returned source performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | access point=>exact point.frame
  | reading same tail point=>exact point.frame
  | written same tail read write=>
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (Queued.update _ _ same) _ _ _ _ _ (update_run read write)
  | continued same tail read write point ih=>
      exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp (Queued.update _ _ same) _ _ _ _ _ (update_run read write))
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
