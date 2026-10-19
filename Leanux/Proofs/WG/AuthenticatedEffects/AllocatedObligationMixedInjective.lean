import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageFreeFrames

/-! A current allocated cell cannot belong to different fixed tickets, whether
its first terminal result has occurred or it remains pending. Multiple physical
queue aliases do not count as new logical tickets. Initialized source transport
is separate from this explicit local uniqueness condition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

/-- Any two tracked claims on one allocation-epoch/cell pair have the same
fixed ticket. The condition includes pending/debt and debt/debt pairs. -/
def MixedInjective (history : List CausalJournal.Event) (ledger : Ledger)
    (debts : List CleanupDebt) : Prop :=
  ∀ first firstPosition firstOrdinal, Tracked ledger debts first firstPosition firstOrdinal →
    ∀ second secondPosition secondOrdinal, Tracked ledger debts second secondPosition secondOrdinal →
      ∀ generation id firstValue secondValue,
        Origin history firstPosition firstOrdinal generation id firstValue →
        Origin history secondPosition secondOrdinal generation id secondValue → first = second

theorem mixed_empty (history : List CausalJournal.Event) : MixedInjective history [] [] := by
  intro ticket position ordinal tracked
  rcases tracked with pending | ⟨outcome,debt,_⟩
  · cases pending
  · cases debt

theorem MixedInjective.pending (mixed : MixedInjective history ledger debts) : Injective history ledger :=
  fun _ _ _ first _ _ _ second _ _ _ _ left right =>
    mixed _ _ _ (Or.inl first) _ _ _ (Or.inl second) _ _ _ _ left right

theorem Tracked.backed (tracked : Tracked ledger debts ticket position ordinal)
    (resident : Resident history ledger w) (cleanup : DebtsResident history ledger debts w) :
    Backed history position ordinal w := by
  rcases tracked with pending | ⟨outcome,debt,_⟩
  · exact resident ticket position ordinal pending
  · exact (cleanup _ debt).2

theorem Tracked.position_lt (tracked : Tracked ledger debts ticket position ordinal)
    (resident : Resident history ledger w) (cleanup : DebtsResident history ledger debts w) :
    position < history.length := by
  obtain ⟨_,_,_,origin,_,_⟩ := tracked.backed resident cleanup
  exact origin.position_lt

/-- With converse coverage, mixed uniqueness gives one fixed logical ticket
for each resident cell, including cells already awaiting terminal cleanup. -/
theorem Covered.unique_ticket (covered : Covered history ledger debts w)
    (mixed : MixedInjective history ledger debts) (cell : PacketMaterial.view w id = some value) :
    ∃ ticket generation position ordinal,
      Packets.epoch w = some generation ∧ Origin history position ordinal generation id value ∧
      Tracked ledger debts ticket position ordinal ∧
      ∀ other otherGeneration otherPosition otherOrdinal otherValue,
        Packets.epoch w = some otherGeneration →
        Origin history otherPosition otherOrdinal otherGeneration id otherValue →
        Tracked ledger debts other otherPosition otherOrdinal → other = ticket := by
  obtain ⟨generation,ticket,position,ordinal,epoch,origin,tracked⟩ := covered id value cell
  refine ⟨ticket,generation,position,ordinal,epoch,origin,tracked,?_⟩
  intro other otherGeneration otherPosition otherOrdinal otherValue otherEpoch otherOrigin otherTracked
  have same : otherGeneration = generation := Option.some.inj (otherEpoch.symm.trans epoch)
  subst otherGeneration
  exact mixed other otherPosition otherOrdinal otherTracked ticket position ordinal tracked
    generation id otherValue value otherOrigin origin

/-- A terminal debt cannot share its current cell with any pending ticket.
The same-ticket possibility is excluded by the fixed ledger's unique status. -/
theorem MixedInjective.unused (mixed : MixedInjective history ledger debts)
    (valid : Valid births ledger) (debt : CleanupDebt) (member : debt ∈ debts)
    (terminal : (debt.ticket,Status.terminal debt.outcome) ∈ ledger)
    (origin : Origin history debt.position debt.ordinal generation id value)
    (epoch : Packets.epoch w = some generation) : Unused history ledger w id := by
  intro other position ordinal pending otherGeneration otherValue otherOrigin otherEpoch
  have sameEpoch : otherGeneration = generation := Option.some.inj (otherEpoch.symm.trans epoch)
  subst otherGeneration
  have sameTicket := mixed other position ordinal (Or.inl pending)
    debt.ticket debt.position debt.ordinal (Or.inr ⟨debt.outcome,by cases debt; exact member,terminal⟩)
    generation id otherValue value otherOrigin origin
  subst other
  have impossible := unique_status (valid.1.symm ▸ valid.2) pending terminal
  cases impossible

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
