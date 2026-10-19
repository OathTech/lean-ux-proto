import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalFreeEntry

/-! Once the actual local batch is empty, removing its empty owner record
changes no physical occurrence or semantic obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG RetirementSecurity

theorem empty_local (phase : TxLocalPhase)
    (before : StagedEntry.Inv history ledger debts (⟨phase,pid,[]⟩ :: locals) w) :
    StagedEntry.Inv history ledger debts locals w :=
  ⟨before.core,before.justified,before.allocationLinks,before.noSelected,
    before.packets,before.coverage,before.inventory.without_first⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
