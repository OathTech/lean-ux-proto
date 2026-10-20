import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationCarrier

/-! The original allocator prefix preserves every staged queue. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal

theorem Path.staged (path : Path packets w a n items v) : Staged.stagedAt v=Staged.stagedAt w :=
  (ProjectedAction.iff_run_ambient _ _ _).mp (allocate_staged (packets.take n)) w a items v a path.native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation

