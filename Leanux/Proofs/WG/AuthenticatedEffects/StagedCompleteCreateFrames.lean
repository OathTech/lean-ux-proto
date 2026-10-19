import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdmissionChecked
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalDebtLoop

/-! Terminal-quiet lifetime accesses at actual refusal key repayment and
physical free. Labelled disposal receipts remain outside these access frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier

theorem key_history (first : SkbId) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (CreateDisposal.keyRepayment first) := by
  unfold CreateDisposal.keyRepayment
  exact Driver.History.product_bind (CompleteSource.focused_history _) (fun _ => CompleteSource.focused_history _)

theorem cleanup_complete (skb : SkbId) (w : World) (before : Complete history ledger) :
    Complete (runPrefix (FirstTerminal.cleanupFree skb) w history).2 ledger :=
  CompleteSource.focused_complete (TxDisposition.nativeAccess (freeTxSkbPrefix skb)) w before

/-- The native cleanup access precedes the labelled receipt. Its exact suffix
extends the entry's history witness without claiming a completed free state. -/
theorem cleanup_prefix (skb : SkbId)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix)) :
    Accounted (history ++ suffix) ledger debts locals w.wg := by
  obtain ⟨actual,extended,quiet⟩ := CreateDisposal.cleanup_birth_quiet skb w history
  rw [performed] at extended
  have same : suffix = actual := List.append_cancel_left extended
  subst actual
  have complete := cleanup_complete skb w before.complete
  rw [performed] at complete
  exact ⟨before.entry.views suffix quiet rfl rfl rfl rfl rfl rfl,complete⟩

/-- The saved native entry is only a history witness here. This does not
assert that a partially executed access returned or preserved its World. -/
theorem focused_entry_history (saved : WGWorld) (body : TxDisposition.Obs α) :
    Driver.ProductHistorySafe (fun h => Inv h ledger debts locals saved) (QueueHandoff.focused body) := by
  intro w h before
  obtain ⟨suffix,extended,quiet⟩ := QueueHandoff.focused_quiet body w h
  have kept : Inv (runPrefix (QueueHandoff.focused body) w h).2 ledger debts locals saved := by
    change (runPrefix (QueueHandoff.focused body) w h).2 = _ at extended
    rw [extended]
    exact before.views suffix quiet rfl rfl rfl rfl rfl rfl
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix (QueueHandoff.focused body) w h).1 with
  | error stop => trivial
  | ok out => exact kept

theorem key_entry_history (saved : WGWorld) (first : SkbId) :
    Driver.ProductHistorySafe (fun h => Inv h ledger debts locals saved) (CreateDisposal.keyRepayment first) := by
  unfold CreateDisposal.keyRepayment
  exact Driver.History.product_bind (focused_entry_history saved _) (fun _ => focused_entry_history saved _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
