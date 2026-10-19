import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryTail

/-! Freeing a pending cell cannot consume any older cleanup debt. Mixed
allocation uniqueness and the ledger's unique status separate that cell from
every terminal obligation, so only its temporary new debt is removed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open Staged.Obligations

theorem pending_forget_old (support : FirstTerminal.Support domain history ledger debts w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    forgetFreedCell history generation skb debts = debts := by
  classical
  unfold forgetFreedCell
  apply List.filter_eq_self.mpr
  intro debt member
  apply decide_eq_true
  intro refers
  obtain ⟨otherValue,otherOrigin⟩ := refers
  have epoch := ((support.resident ticket position ordinal pending).at_origin origin).1
  have unused := support.mixed.unused support.valid debt member (support.cleanup debt member).1 otherOrigin epoch
  exact unused ticket position ordinal pending generation value origin epoch

/-- The source-labelled free's temporary terminal debt is the only debt
removed. The original list, including its order and multiplicities, survives. -/
theorem pending_forget_new (support : FirstTerminal.Support domain history ledger debts w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value)
    (outcome : Staged.Obligations.Terminal) :
    forgetFreedCell history generation skb (⟨ticket,position,ordinal,outcome⟩ :: debts) = debts := by
  classical
  have refers : (⟨ticket,position,ordinal,outcome⟩ : CleanupDebt).Refers history generation skb := ⟨value,origin⟩
  have same : forgetFreedCell history generation skb (⟨ticket,position,ordinal,outcome⟩ :: debts) =
      forgetFreedCell history generation skb debts := by
    simp only [forgetFreedCell,List.filter_cons,refers,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
  exact same.trans (pending_forget_old support pending origin)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
