import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOwnerWriteSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeLookup

/-! The two owner-word locations retain the same TX packet account at every
named read/write point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OwnerWrite
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Point.frame (point : Point owner peer w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | handshake point=>exact point.frame
  | keypair point=>exact point.frame
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (HandshakeLookup.owner_write owner peer) _ _ _ _ _ performed


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OwnerWrite
