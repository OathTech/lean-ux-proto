import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueCompositionSource

/-! The offered-ring event is a total observation after the native return;
it cannot introduce another stopped branch or change the ownership phase. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations

theorem offered_total (items : List SkbId) (ret : Int)
    (owned : Owned ledger debts locals history w) :
    ∃ suffix, runPrefix (focused (offered items ret)) w history = (.ok (ret,w),history ++ suffix) ∧
      Owned ledger debts locals (history ++ suffix) w := by
  have same := focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent? (offered_erases items ret) w history
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (offered items ret) w history
  refine ⟨suffix,Prod.ext same extended,owned.1.quiet_views suffix quiet rfl rfl rfl,owned.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
