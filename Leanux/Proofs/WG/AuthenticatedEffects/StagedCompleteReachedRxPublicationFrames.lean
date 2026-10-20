import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxPublicationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerBorrowFrames

/-! Receive publication preserves the same TX account at each native cut. The final saved-peer write is justified by its actual complete source prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxPublicationAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Point.frame (point : Point skb state w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | resolving point=>exact point.frame
  | borrowing resolved point=>
      exact point.frame.trans ((ProjectedAction.iff_run_ambient _ _ _).mp (resolveShape skb).frame _ _ _ _ _ resolved)
  | preparing resolved borrowed point=>
      exact point.frame.trans (((ProjectedAction.iff_run_ambient _ _ _).mp (Queued.acquire _) _ _ _ _ _ borrowed).trans
        ((ProjectedAction.iff_run_ambient _ _ _).mp (resolveShape skb).frame _ _ _ _ _ resolved))
  | written resolved borrowed prepared written=>
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (CompleteDecrypt.publication skb state) _ _ _ _ _
        (written_return resolved borrowed prepared written)
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (CompleteDecrypt.publication skb state) _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxPublicationAccess
