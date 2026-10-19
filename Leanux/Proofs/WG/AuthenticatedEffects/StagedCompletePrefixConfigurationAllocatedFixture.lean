import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationAllocated
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedFixture

/-! Actual fixture markers retain the same allocation companion and add
one certified journal cut each; the body has its own prefix contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationAllocatedFixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
open ConfigurationAllocated (Checked)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event→Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w→Safe h)
include accountSafe

theorem enter (cause : Cause) : Checked debts locals Safe (CausalScope.enterState Event.scope cause) := by
  intro w a h before
  have kept := CompleteAllocatedFixture.marker (.entered ⟨h.length,cause⟩) before.1
  have safe := CompleteAllocatedFixture.scope_safe Safe accountSafe _ _ _ kept
  have all := before.2.append (Cuts.singleton before.2.last safe)
  exact ⟨[_],rfl,all,kept,all⟩

theorem leave (position : Nat) : Checked debts locals Safe (CausalScope.leaveState Event.scope position) := by
  intro w a h before
  have kept := CompleteAllocatedFixture.marker (.exited position) before.1
  have safe := CompleteAllocatedFixture.scope_safe Safe accountSafe _ _ _ kept
  have all := before.2.append (Cuts.singleton before.2.last safe)
  exact ⟨[_],rfl,all,kept,all⟩

theorem run (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  exact StateEnsures.bind (enter Safe accountSafe (.fixture trigger)) (fun position=>
    StateEnsures.bind checked (fun value=>StateEnsures.bind (leave Safe accountSafe position)
      (fun _=>ConfigurationAllocated.pure_checked Safe value)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationAllocatedFixture
