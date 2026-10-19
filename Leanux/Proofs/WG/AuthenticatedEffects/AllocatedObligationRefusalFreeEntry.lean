import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalFreeFrames
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
theorem labelled_free_entry (reason : Terminal.Reason) (skb : SkbId) (phase : TxLocalPhase)
    (performed : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (before : StagedEntry.Inv history ledger debts (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let cutHistory := history ++ suffix
    let outcome := Staged.Obligations.Terminal.disposed cutHistory.length reason
    let afterLedger := settle [ticket] outcome ledger
    let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
    let afterDebts := forgetFreedCell cutHistory generation skb (debt :: debts)
    let journal := cutHistory ++ [CausalJournal.Event.terminalDrop receipt]
    runPrefix (free reason skb) w history = (.ok ((),v),journal) ∧
      Staged.Obligations.Step ledger afterLedger ∧
      StagedEntry.Inv journal afterLedger afterDebts (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
      (ticket,Status.terminal outcome) ∈ afterLedger := by
  dsimp only
  let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
  obtain ⟨native,_⟩ := FirstTerminal.labelled_cut reason skb w v history suffix performed
  obtain ⟨actualSuffix,extended,quiet⟩ := cleanup_birth_quiet skb w history
  rw [performed] at extended
  have same : suffix = actualSuffix := List.append_cancel_left extended
  subst actualSuffix
  have atPrefix := before.views suffix quiet rfl rfl rfl rfl rfl rfl
  have evidence : StagedProvenance.At (history ++ suffix) (.terminalDrop receipt) ticket
      (.disposed (history ++ suffix).length reason) :=
    .disposed receipt native position ordinal generation value
      ((atPrefix.allocationLinks ticket position ordinal pending).at_origin (origin.append suffix))
      (atPrefix.core.physical.resident ticket position ordinal pending)
  have settled := CompletionBatch.entry_settle_allocated atPrefix pending evidence rfl
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.core.physical,before.core.valid⟩
  obtain ⟨observed,step,physical,terminal,_,_⟩ :=
    FirstTerminal.labelled_debt reason skb w v history suffix performed support pending origin
  have geometry := free_views receipt native
  obtain ⟨coverage,inventory,bounded⟩ := free_owner phase before.coverage before.inventory before.packets native
  refine ⟨observed,step,?_,terminal⟩
  exact ⟨⟨settled.core.valid,settled.core.queues.views geometry.1 (free_staged receipt native),
    settled.core.selected,physical.toPhysical⟩,settled.justified,settled.allocationLinks,
    settled.noSelected,bounded,coverage,inventory⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
