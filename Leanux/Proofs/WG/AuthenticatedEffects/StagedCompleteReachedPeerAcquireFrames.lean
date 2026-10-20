import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerAcquireSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeLookup

/-! Each acquisition point keeps the TX ticket projection. The write is
related to its actual successful front, including the saved peer record. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerAcquire
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Point.frame (point : Point peer w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | front point=>exact point.frame
  | written prepared written=>
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (HandshakeLookup.maybe_peer peer) _ _ _ _ _
        (written_return prepared written)
  | returned performed=>
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (HandshakeLookup.maybe_peer peer) _ _ _ _ _ performed


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerAcquire
