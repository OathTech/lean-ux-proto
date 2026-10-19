import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveAllocation
import Leanux.Proofs.WG.RetirementSecurity.TxCoverage

/-! Converse physical coverage of fixed allocated obligations. A first terminal
result does not free the native cell: its exact allocation remains represented
as cleanup debt until the actual free. These are local state/history carriers;
source terminal attribution and initialized transport are separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

structure CleanupDebt where
  ticket : Ticket
  position : Nat
  ordinal : Nat
  outcome : TransmitSecurity.Staged.Obligations.Terminal

/-- An allocated occurrence is either pending or has a retained first result
and an explicit physical cleanup obligation. -/
def Tracked (ledger : Ledger) (debts : List CleanupDebt) (ticket : Ticket)
    (position ordinal : Nat) : Prop :=
  (ticket,Status.pending (.allocated position ordinal)) ∈ ledger ∨
    ∃ outcome, (⟨ticket,position,ordinal,outcome⟩ : CleanupDebt) ∈ debts ∧
      (ticket,Status.terminal outcome) ∈ ledger

/-- Every resident TX cell has an exact allocation occurrence assigned to one
fixed ticket. Device-ring aliases cannot manufacture another assignment. -/
def Covered (history : List CausalJournal.Event) (ledger : Ledger)
    (debts : List CleanupDebt) (w : WGWorld) : Prop :=
  ∀ id value, PacketMaterial.view w id = some value →
    ∃ generation ticket position ordinal,
      Packets.epoch w = some generation ∧
      Origin history position ordinal generation id value ∧ Tracked ledger debts ticket position ordinal

/-- Every retained cleanup debt still has its native cell and unchanged first
terminal outcome. A free must discharge this debt, not merely erase storage. -/
def DebtsResident (history : List CausalJournal.Event) (ledger : Ledger)
    (debts : List CleanupDebt) (w : WGWorld) : Prop :=
  ∀ debt ∈ debts, (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧
    Backed history debt.position debt.ordinal w

theorem Covered.pending (covered : Covered history ledger [] w)
    (cell : PacketMaterial.view w id = some value) :
    ∃ generation ticket position ordinal,
      Packets.epoch w = some generation ∧ Origin history position ordinal generation id value ∧
      (ticket,Status.pending (.allocated position ordinal)) ∈ ledger := by
  obtain ⟨generation,ticket,position,ordinal,epoch,origin,tracked⟩ := covered id value cell
  refine ⟨generation,ticket,position,ordinal,epoch,origin,?_⟩
  rcases tracked with pending | ⟨outcome,debt,_⟩
  · exact pending
  · cases debt

theorem covered_initial (net bare : Bool) : Covered [] [] [] (Runner.initialWG net bare) := by
  intro id value cell
  cases net <;> cases bare <;> simp [PacketMaterial.view,TxDisposition.txPackets,Runner.initialWG] at cell

theorem debts_empty (history : List CausalJournal.Event) (ledger : Ledger) (w : WGWorld) :
    DebtsResident history ledger [] w := by
  intro debt member
  cases member

/-- Historical ticket coverage and native logical ownership are independent
facts. Their join places each covered cell in a peer queue or a caller local. -/
theorem Covered.owned (covered : Covered history ledger debts w)
    (ownership : RetirementSecurity.TxCoverage locals w)
    (cell : PacketMaterial.view w id = some value) :
    (∃ generation ticket position ordinal,
      Packets.epoch w = some generation ∧ Origin history position ordinal generation id value ∧
      Tracked ledger debts ticket position ordinal) ∧ RetirementSecurity.TxOwned locals w id := by
  obtain ⟨packet,resident,_⟩ := Option.map_eq_some_iff.mp cell
  exact ⟨covered id value cell,ownership id packet resident⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
