import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxAccountingSource

/-! Byte accounting preserves the same completed socket settlement and
cleanup debt at all fixed native access points and at its normal endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal CompleteCarrier StagedTerminalComplete

theorem returned_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (action pid packet ret) w h=(.ok (sent,u),middle)) : Accounted middle ledger debts locals u.wg := by
  obtain ⟨suffix,grown⟩:=Appends.focus FirstTerminal.encode CausalJournal.completion? (afterSocket pid packet ret) w h
  have free:=focus_birth_free FirstTerminal.encode CausalJournal.completion? completion_encode_births
    (afterSocket pid packet ret) w h suffix grown
  have paired:=Converse.history_preserved before.complete (Appends.focus _ _ _)
    (accounting_history_quiet pid packet ret) (w:=w)
  change Complete (runPrefix (action pid packet ret) w h).2 ledger at paired
  rw [performed] at paired
  have native := (focusPrefix_erases FirstTerminal.encode CausalJournal.completion?
    (FirstTerminal.accounting_erases pid packet ret) w h).symm.trans (congrArg Prod.fst performed)
  have same := (ProjectedAction.iff_run _ _ _).mp (accounting_entry_view pid packet ret) _ _ _ native
  change (runPrefix (action pid packet ret) w h).2=h++suffix at grown
  rw [performed] at grown
  refine ⟨?_,paired⟩
  rw [show middle=h++suffix from grown]
  exact Queued.Inv.history (before.entry.same_view same) suffix free

/-- Security: a byte-counter update cannot discard or duplicate the socket
outcome, selected packet or cleanup debt, including its silent write interval. -/
theorem Point.accounted (before : Accounted h ledger debts locals w.wg)
    (point : Point pid packet ret w h u middle) : Accounted middle ledger debts locals u.wg := by
  cases point with
  | entry=>exact before
  | guarded=>exact before
  | update successful point=>
      have guarded : Accounted h ledger debts locals (guardedWorld ret w).wg := before
      exact point.accounted guarded
  | returned performed=>exact returned_accounted before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccounting
