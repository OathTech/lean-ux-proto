import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteSettlement

/-! Each actual labelled free settles exactly its one pending ticket while
restoring the original debt list. Complete and native Entry use the identical
successor, after the exact lifetime-access suffix and terminal receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open HandshakeSecurity.StagedConservation

/-- A source-labelled free has exactly one accounted terminal ticket at its
actual receipt position; it preserves every older terminal count and restores
the caller's original debts after removing this cell. -/
theorem labelled_free (reason : Terminal.Reason) (skb : SkbId) (phase : TxLocalPhase)
    (performed : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (before : Accounted history ledger debts (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let cutHistory := history ++ suffix
    let outcome := Staged.Obligations.Terminal.disposed cutHistory.length reason
    let afterLedger := settle [ticket] outcome ledger
    let journal := cutHistory ++ [CausalJournal.Event.terminalDrop receipt]
    runPrefix (CreateDisposal.free reason skb) w history = (.ok ((),v),journal) ∧
      Staged.Obligations.Step ledger afterLedger ∧
      Accounted journal afterLedger debts (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
      (ticket,Status.terminal outcome) ∈ afterLedger := by
  dsimp only
  obtain ⟨observed,step,entry,terminal⟩ :=
    CreateDisposal.labelled_free_entry_exact reason skb phase performed before.entry pending origin
  have atPrefix := cleanup_prefix skb before performed
  refine ⟨observed,step,⟨entry,?_⟩,terminal⟩
  apply atPrefix.complete.settle_cut
    (chosen := [ticket])
    (requested := ⟨.disposed (history ++ suffix).length reason,1⟩)
    atPrefix.entry.core.valid atPrefix.entry.justified (by simp)
  · intro other member
    cases List.mem_singleton.mp member
    exact ⟨_,pending⟩
  · rfl
  · rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
