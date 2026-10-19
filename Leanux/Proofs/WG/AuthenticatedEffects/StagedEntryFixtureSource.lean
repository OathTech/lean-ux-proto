import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourcePassive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Fixture scope markers transport the existing packet accounting. The
native driver determines the actual trigger site; a marker creates no ticket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.FixtureSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal SourcePassive

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem enter (cause : CausalSources.Cause) :
    Checked debts locals Safe (CausalScope.enterState Event.scope cause) := by
  apply CausalScope.enterState_preserves
  · intro h w a before
    obtain ⟨ledger,entry⟩ := before
    exact entrySafe ledger h w entry
  · intro event h w a before
    obtain ⟨ledger,entry⟩ := before
    exact ⟨ledger,Queued.Inv.history entry [.scope event] (by simp [Staged.Obligations.birthPackets])⟩

theorem leave (position : Nat) :
    Checked debts locals Safe (CausalScope.leaveState Event.scope position) :=
  fixed Safe entrySafe (fun _ => Passive.emit (.scope (.exited position)) rfl)

theorem run (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  exact bind_checked Safe (enter Safe entrySafe (.fixture trigger)) (fun position =>
    bind_checked Safe checked (fun value =>
      bind_checked Safe (leave Safe entrySafe position) (fun _ => pure_checked Safe entrySafe value)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.FixtureSource
