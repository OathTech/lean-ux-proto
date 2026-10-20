import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessSource

/-! The adapter source gives unchanged projection before write-back, or an actual completed native run afterward. RX allocation and erasure use the latter account contract, without claiming a store equality. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SkbAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

/-- Before the adapter's single write-back, component execution has only
Ambient state by type. After that write the fixed suffix is pure return. -/
theorem Point.same_or_returned (point : Point action w a v b) :
    StagedEntry.view v=StagedEntry.view w ∨ ∃value,((liftSkb action).run w).run a=.ok ((value,v),b) := by
  cases point with
  | read point=>exact Or.inl point.frame
  | component device performed=>exact Or.inl rfl
  | returned performed=>exact Or.inr ⟨_,performed⟩

theorem Point.frame (frame : SameView StagedEntry.view (liftSkb action)) (point : Point action w a v b) :
    StagedEntry.view v=StagedEntry.view w := by
  rcases point.same_or_returned with same|⟨value,performed⟩
  · exact same
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp frame _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SkbAccess
