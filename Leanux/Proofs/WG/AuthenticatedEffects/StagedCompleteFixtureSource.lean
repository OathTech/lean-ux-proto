import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Fixture scope markers transport the paired packet accounting. The
native driver determines the actual trigger site; a marker creates no ticket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePassive

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem enter (cause : CausalSources.Cause) :
    Checked debts locals Safe (CausalScope.enterState Event.scope cause) := by
  apply CausalScope.enterState_preserves
  · intro h w a before
    obtain ⟨ledger,entry⟩ := before
    exact accountSafe ledger h w entry
  · intro event h w a before
    obtain ⟨ledger,entry⟩ := before
    exact ⟨ledger,entry.append_quiet [.scope event] (by simp [Staged.Obligations.birthPackets]) (by intro e member position; simp only [List.mem_singleton] at member; subst e; rfl)⟩

theorem leave (position : Nat) :
    Checked debts locals Safe (CausalScope.leaveState Event.scope position) :=
  emit Safe accountSafe (.scope (.exited position)) rfl (fun _ => rfl)

theorem run (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  exact bind_checked Safe (enter Safe accountSafe (.fixture trigger)) (fun position =>
    bind_checked Safe checked (fun value =>
      bind_checked Safe (leave Safe accountSafe position) (fun _ => pure_checked Safe accountSafe value)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFixture
