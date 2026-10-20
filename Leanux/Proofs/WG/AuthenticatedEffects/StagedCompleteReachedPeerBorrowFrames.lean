import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerBorrowSource

/-! The reference write changes only metadata of the peer read by this acquisition. Every point preserves the staged and allocated TX projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerBorrowAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Point.frame (point : Point pid w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | front point=>exact point.frame
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (Queued.acquire pid) _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerBorrowAccess
