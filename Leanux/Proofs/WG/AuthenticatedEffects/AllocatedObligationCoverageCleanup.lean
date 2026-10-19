import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageSettlement

/-! Cleanup removes only debts naming the cell actually freed. This logical
filter does not retire a pending ticket and never changes a first outcome. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

def CleanupDebt.Refers (history : List CausalJournal.Event) (generation id : Nat)
    (debt : CleanupDebt) : Prop :=
  ∃ value, Origin history debt.position debt.ordinal generation id value

noncomputable def forgetFreedCell (history : List CausalJournal.Event) (generation id : Nat)
    (debts : List CleanupDebt) : List CleanupDebt := by
  classical
  exact debts.filter (fun debt => decide (¬ debt.Refers history generation id))

theorem mem_forgetFreedCell : debt ∈ forgetFreedCell history generation id debts ↔
    debt ∈ debts ∧ ¬ debt.Refers history generation id := by
  classical
  simp only [forgetFreedCell,List.mem_filter,decide_eq_true_eq]

/-- If an actual resident cell has no pending claimant, converse coverage
requires an explicit terminal cleanup debt for that same allocation occurrence. -/
theorem Covered.requires_debt (covered : Covered history ledger debts w)
    (unused : Unused history ledger w id) (cell : PacketMaterial.view w id = some value) :
    ∃ debt ∈ debts, (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧
      ∃ generation, Packets.epoch w = some generation ∧
        Origin history debt.position debt.ordinal generation id value := by
  obtain ⟨generation,ticket,position,ordinal,epoch,origin,tracked⟩ := covered id value cell
  rcases tracked with pending | ⟨outcome,debt,terminal⟩
  · exact False.elim (unused ticket position ordinal pending generation value origin epoch)
  · exact ⟨⟨ticket,position,ordinal,outcome⟩,debt,terminal,generation,epoch,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
