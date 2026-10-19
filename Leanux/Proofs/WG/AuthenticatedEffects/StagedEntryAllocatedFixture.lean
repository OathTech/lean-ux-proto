import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationReady

/-! Fixture scopes change only the journal and preserve the allocation
companion while their actual body carries packet accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.AllocatedFixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal AllocatedCarrier

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem scope_safe : ∀ h w a, Carrier debts locals h w a → Safe h := by
  intro h w a before
  obtain ⟨ledger,entry⟩ := before.1
  exact entrySafe ledger h w entry

omit entrySafe in
theorem marker (event : CausalScope.Event Cause) (before : Carrier debts locals h w a) :
    Carrier debts locals (h ++ [.scope event]) w a := by
  obtain ⟨⟨ledger,entry⟩,allocated⟩ := before
  exact ⟨⟨ledger,Queued.Inv.history entry [.scope event] (by simp [Staged.Obligations.birthPackets])⟩,allocated⟩

theorem run (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply StatePrefixEnsures.bind
    (CausalScope.enterState_preserves Event.scope _ (scope_safe Safe entrySafe)
      (fun event _ _ _ before => marker event before))
  intro position
  apply StatePrefixEnsures.bind checked
  intro value
  apply StatePrefixEnsures.bind
    (CausalScope.leaveState_preserves Event.scope position (scope_safe Safe entrySafe)
      (fun event _ _ _ before => marker event before))
  intro ignored
  exact ConfigurationReady.pure_checked Safe entrySafe value

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.AllocatedFixture
