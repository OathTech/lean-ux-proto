import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointEntry

/-! Source coverage is derived from the entry account and actual execution.
It retains the same account indices and the original result at every remainder;
an error has no fabricated returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem source_covered
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix (source pid timer expires clock unit) w h = (result,last)) :
    SourceExecution pid timer expires clock unit w h result last ∧
    ∀ site u middle, SourcePoint pid timer expires clock unit w h site u middle →
      CompleteCarrier.Accounted middle ledger debts locals u.wg ∧
      ∃ remainder, SourceResidual pid timer expires clock unit w h site u middle remainder ∧
        runPrefix remainder u middle = (result,last) := by
  refine ⟨source_cases performed,?_⟩
  intro site u middle point
  obtain ⟨remainder,remaining⟩ := point.residual
  exact ⟨point.accounted before,remainder,remaining,remaining.run.symm.trans performed⟩

theorem stopped_covered
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix (source pid timer expires clock unit) w h = (.error reason,last)) :
    SourceExecution pid timer expires clock unit w h (.error reason) last ∧
    ∀ site u middle, SourcePoint pid timer expires clock unit w h site u middle →
      CompleteCarrier.Accounted middle ledger debts locals u.wg ∧
      ∃ remainder, SourceResidual pid timer expires clock unit w h site u middle remainder ∧
        runPrefix remainder u middle = (.error reason,last) :=
  source_covered before performed

theorem returned_covered
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix (source pid timer expires clock unit) w h = (.ok ((),v),last)) :
    SourceExecution pid timer expires clock unit w h (.ok ((),v)) last ∧
    ∀ site u middle, SourcePoint pid timer expires clock unit w h site u middle →
      CompleteCarrier.Accounted middle ledger debts locals u.wg ∧
      ∃ remainder, SourceResidual pid timer expires clock unit w h site u middle remainder ∧
        runPrefix remainder u middle = (.ok ((),v),last) :=
  source_covered before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
