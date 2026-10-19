import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageFrames

/-! The first terminal cut preserves a resident allocation as explicit cleanup
debt. Its source caller must supply the actual terminal receipt and outcome;
these ledger laws neither invent that receipt nor classify a native failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

private theorem one_step (valid : Valid births ledger)
    (pending : (ticket,Status.pending location) ∈ ledger) (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    TransmitSecurity.Staged.Obligations.Step ledger (settle [ticket] outcome ledger) := by
  apply settle_pending (valid.1.symm ▸ valid.2)
  intro other member
  have same : other = ticket := by simpa using member
  exact same ▸ mem_pendingAt.mpr pending

private theorem settled_member (pending : (ticket,Status.pending location) ∈ ledger)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    (ticket,Status.terminal outcome) ∈ settle [ticket] outcome ledger := by
  exact List.mem_map.mpr ⟨_,pending,by simp⟩

theorem Tracked.settle (valid : Valid births ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (tracked : Tracked ledger debts other otherPosition otherOrdinal)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    Tracked (settle [ticket] outcome ledger) (⟨ticket,position,ordinal,outcome⟩ :: debts)
      other otherPosition otherOrdinal := by
  rcases tracked with otherPending | ⟨previous,debt,terminal⟩
  · by_cases same : other = ticket
    · subst other
      have status := unique_status (valid.1.symm ▸ valid.2) otherPending pending
      obtain ⟨rfl,rfl⟩ := Pending.allocated.inj (Status.pending.inj status)
      exact Or.inr ⟨outcome,List.mem_cons_self ..,settled_member pending outcome⟩
    · exact Or.inl (List.mem_map.mpr ⟨_,otherPending,by simp [same]⟩)
  · exact Or.inr ⟨previous,List.mem_cons_of_mem _ debt,(one_step valid pending outcome).terminal terminal⟩

/-- Settling this exact pending allocation does not discard its resident cell:
the same ticket/position/ordinal moves to the cleanup-debt alternative. -/
theorem Covered.settle (covered : Covered history ledger debts w)
    (valid : Valid births ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    Covered history (settle [ticket] outcome ledger)
      (⟨ticket,position,ordinal,outcome⟩ :: debts) w := by
  intro id value cell
  obtain ⟨generation,other,batch,index,epoch,origin,tracked⟩ := covered id value cell
  exact ⟨generation,other,batch,index,epoch,origin,tracked.settle valid pending outcome⟩

/-- Physical backing of the new debt comes from the existing pending ticket,
not from terminal membership alone. Previously settled outcomes remain fixed. -/
theorem DebtsResident.settle (debtsResident : DebtsResident history ledger debts w)
    (resident : Resident history ledger w) (valid : Valid births ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    DebtsResident history (settle [ticket] outcome ledger)
      (⟨ticket,position,ordinal,outcome⟩ :: debts) w := by
  intro debt member
  rcases List.mem_cons.mp member with same | old
  · subst debt
    exact ⟨settled_member pending outcome,resident ticket position ordinal pending⟩
  · obtain ⟨terminal,backed⟩ := debtsResident debt old
    exact ⟨(one_step valid pending outcome).terminal terminal,backed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
