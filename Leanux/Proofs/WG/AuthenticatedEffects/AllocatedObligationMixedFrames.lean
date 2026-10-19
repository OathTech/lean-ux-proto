import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedInjective

/-! History extension, first-terminal settlement and actual debt removal keep
the same logical ticket for every tracked allocation. Settlement does not
reassign a cell, and cleanup only removes tracked claims. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

theorem MixedInjective.append (mixed : MixedInjective history ledger debts)
    (resident : Resident history ledger w) (cleanup : DebtsResident history ledger debts w)
    (suffix : List CausalJournal.Event) : MixedInjective (history ++ suffix) ledger debts := by
  intro first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
    generation id firstValue secondValue firstOrigin secondOrigin
  exact mixed first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
    generation id firstValue secondValue
    (firstOrigin.prefix (firstTracked.position_lt resident cleanup))
    (secondOrigin.prefix (secondTracked.position_lt resident cleanup))

theorem Tracked.before_settle (cleanup : DebtsResident history ledger debts w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (tracked : Tracked (TransmitSecurity.Staged.Obligations.settle [ticket] outcome ledger)
      (⟨ticket,position,ordinal,outcome⟩ :: debts) other otherPosition otherOrdinal) :
    Tracked ledger debts other otherPosition otherOrdinal := by
  rcases tracked with afterPending | ⟨previous,member,_⟩
  · exact Or.inl (pending_after_settle [ticket] outcome afterPending).1
  · rcases List.mem_cons.mp member with same | old
    · have ticketEq := congrArg CleanupDebt.ticket same
      have positionEq := congrArg CleanupDebt.position same
      have ordinalEq := congrArg CleanupDebt.ordinal same
      dsimp only at ticketEq positionEq ordinalEq
      subst other
      subst otherPosition
      subst otherOrdinal
      exact Or.inl pending
    · exact Or.inr ⟨previous,old,(cleanup _ old).1⟩

/-- Moving a pending allocation to terminal cleanup preserves its original
ticket; no first-terminal record can activate another ticket's cell claim. -/
theorem MixedInjective.settle (mixed : MixedInjective history ledger debts)
    (cleanup : DebtsResident history ledger debts w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    MixedInjective history (TransmitSecurity.Staged.Obligations.settle [ticket] outcome ledger)
      (⟨ticket,position,ordinal,outcome⟩ :: debts) := by
  intro first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
    generation id firstValue secondValue firstOrigin secondOrigin
  exact mixed first firstPosition firstOrdinal (firstTracked.before_settle cleanup pending)
    second secondPosition secondOrdinal (secondTracked.before_settle cleanup pending)
    generation id firstValue secondValue firstOrigin secondOrigin

theorem Tracked.before_forget
    (tracked : Tracked ledger (forgetFreedCell history generation id debts) ticket position ordinal) :
    Tracked ledger debts ticket position ordinal := by
  rcases tracked with pending | ⟨outcome,member,terminal⟩
  · exact Or.inl pending
  · exact Or.inr ⟨outcome,(mem_forgetFreedCell.mp member).1,terminal⟩

/-- Cleanup cannot authorize another fixed ticket for any surviving cell. -/
theorem MixedInjective.forget (mixed : MixedInjective history ledger debts)
    (generation id : Nat) : MixedInjective history ledger (forgetFreedCell history generation id debts) := by
  intro first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
    epoch skb firstValue secondValue firstOrigin secondOrigin
  exact mixed first firstPosition firstOrdinal firstTracked.before_forget
    second secondPosition secondOrdinal secondTracked.before_forget epoch skb firstValue secondValue firstOrigin secondOrigin

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
