import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalDebtFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSettlement
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalAllocatedCuts

/-! The actual labelled free transports the complete canonical entry: source
terminal evidence, allocation ancestry, no detached staging tickets, packet
bounds, and the remaining native owner all refer to the same fixed ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

/-- One actual labelled refusal free records its first terminal and advances
the caller-local batch by exactly that cell. All semantic and physical parts
of the canonical entry survive together; no cleanup or ownership premise is
substituted for the native operation. -/
theorem labelled_free_entry_exact (reason : Terminal.Reason) (skb : SkbId) (phase : TxLocalPhase)
    (performed : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (before : StagedEntry.Inv history ledger debts (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let cutHistory := history ++ suffix
    let outcome := Staged.Obligations.Terminal.disposed cutHistory.length reason
    let afterLedger := settle [ticket] outcome ledger
    let journal := cutHistory ++ [CausalJournal.Event.terminalDrop receipt]
    runPrefix (free reason skb) w history = (.ok ((),v),journal) ∧
      Staged.Obligations.Step ledger afterLedger ∧
      StagedEntry.Inv journal afterLedger debts (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
      (ticket,Status.terminal outcome) ∈ afterLedger := by
  have result := labelled_free_entry reason skb phase performed before pending origin
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.core.physical,before.core.valid⟩
  have restored := pending_forget_new (support.append suffix) pending (origin.append suffix)
    (.disposed (history ++ suffix).length reason)
  simpa only [restored] using result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
