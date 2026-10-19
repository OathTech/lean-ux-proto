import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSendLoop

/-! Ordinary cleanup preserves the exact first-terminal ledger while removing
the physical debts. Its actual access observer has no terminal demand; it is
not treated as another labelled disposal or another socket outcome. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts StagedTerminalComplete
open HandshakeSecurity.StagedDisposal

theorem cleanup_quiet (skb : SkbId) : HistoryFrame ledgerEvent? (FirstTerminal.cleanupFree skb) :=
  focusPrefix_other _ _ _ (fun _ => rfl) _

theorem cleanup_complete (complete : Complete history ledger) (skb : SkbId) (w : World) :
    Complete (runPrefix (FirstTerminal.cleanupFree skb) w history).2 ledger :=
  history_preserved complete (Appends.focus _ _ _) (cleanup_quiet skb)

theorem freeLoop_quiet (remaining : List SkbId) :
    HistoryFrame ledgerEvent? (freeLoop (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal) remaining) := by
  induction remaining with
  | nil => exact HistoryFrame.pure _ _
  | cons skb rest ih =>
    change HistoryFrame ledgerEvent? (FirstTerminal.cleanupFree skb >>= fun _ => _)
    exact HistoryFrame.bind (cleanup_quiet skb) (fun _ => ih)

theorem freeLoop_total (remaining : List SkbId)
    (before : Owned context (.freeing remaining) history ledger debts w)
    (localDebts : LocalDebts context remaining debts)
    (complete : Complete history ledger) :
    ∃ v suffix,
      runPrefix (freeLoop (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal) remaining) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing []) (history ++ suffix) ledger [] v ∧
      Complete (history ++ suffix) ledger := by
  obtain ⟨v,suffix,performed,after⟩ := indexed_freeLoop_total remaining before localDebts
  refine ⟨v,suffix,performed,after,?_⟩
  have quiet := freeLoop_quiet remaining w history
  rw [performed] at quiet
  exact extension complete rfl quiet

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
