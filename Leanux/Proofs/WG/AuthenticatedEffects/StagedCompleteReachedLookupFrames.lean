import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLookupSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerAcquireFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOwnerWriteFrames

/-! Every lookup point preserves the complete ticket projection, including
points reached before a later failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.frame (source : Shape action) : SameView StagedEntry.view action := by
  induction source with
  | access source=>exact source.frame
  | acquire peer=>exact HandshakeLookup.maybe_peer peer
  | ownerWrite owner peer=>exact HandshakeLookup.owner_write owner peer
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.frame (point : Point source w a v b) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry source=>rfl
  | returned source performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | access point=>exact point.frame
  | acquire point=>exact point.frame
  | ownerWrite point=>exact point.frame
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
