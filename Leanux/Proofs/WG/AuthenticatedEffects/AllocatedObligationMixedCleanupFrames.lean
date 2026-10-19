import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedFrames

/-! The native cleanup caller derives its no-pending-alias obligation from
mixed ticket uniqueness. Physical free cannot give a surviving cell a different
ticket or revise any first terminal result in the unchanged ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

/-- Free the exact resident terminal debt. The original native receipt and
allocation origin identify the cell; mixed uniqueness discharges Unused. -/
theorem cleanup_mixed (receipt : Terminal.Receipt) (native : receipt.Valid)
    (validLedger : Valid births ledger) (mixed : MixedInjective history ledger debts)
    (resident : Resident history ledger receipt.run.before.wg)
    (covered : Covered history ledger debts receipt.run.before.wg)
    (cleanup : DebtsResident history ledger debts receipt.run.before.wg)
    (debt : CleanupDebt) (member : debt ∈ debts)
    (origin : Origin history debt.position debt.ordinal generation receipt.skb value)
    (epoch : Packets.epoch receipt.run.before.wg = some generation) :
    let afterDebts := forgetFreedCell history generation receipt.skb debts
    Resident history ledger receipt.run.after.wg ∧ MixedInjective history ledger afterDebts ∧
      Covered history ledger afterDebts receipt.run.after.wg ∧
      DebtsResident history ledger afterDebts receipt.run.after.wg ∧
      (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧
      debt ∉ afterDebts := by
  have terminal := (cleanup debt member).1
  have unused := mixed.unused validLedger debt member terminal origin epoch
  have result := cleanup_covered receipt native covered resident cleanup unused epoch
  refine ⟨result.2.1,mixed.forget generation receipt.skb,result.2.2.1,result.2.2.2,terminal,?_⟩
  intro retained
  exact (mem_forgetFreedCell.mp retained).2 ⟨value,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
