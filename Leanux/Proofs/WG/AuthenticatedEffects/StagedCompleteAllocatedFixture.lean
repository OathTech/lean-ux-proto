import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationReady

/-! Fixture scopes change only the journal and preserve the allocation
companion while their actual body carries packet accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteAllocatedFixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompleteAllocated

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem scope_safe : ∀ h w a, Carrier debts locals h w a → Safe h := by
  intro h w a before
  obtain ⟨ledger,entry⟩ := before.1
  exact accountSafe ledger h w entry

omit accountSafe in
theorem marker (event : CausalScope.Event Cause) (before : Carrier debts locals h w a) :
    Carrier debts locals (h ++ [.scope event]) w a := by
  obtain ⟨⟨ledger,entry⟩,allocated⟩ := before
  exact ⟨⟨ledger,entry.append_quiet [.scope event] (by simp [Staged.Obligations.birthPackets]) (by intro e member position; simp only [List.mem_singleton] at member; subst e; rfl)⟩,allocated⟩

theorem run (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply StatePrefixEnsures.bind
    (CausalScope.enterState_preserves Event.scope _ (scope_safe Safe accountSafe)
      (fun event _ _ _ before => marker event before))
  intro position
  apply StatePrefixEnsures.bind checked
  intro value
  apply StatePrefixEnsures.bind
    (CausalScope.leaveState_preserves Event.scope position (scope_safe Safe accountSafe)
      (fun event _ _ _ before => marker event before))
  intro ignored
  exact CompleteConfigurationReady.pure_checked Safe accountSafe value

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteAllocatedFixture
