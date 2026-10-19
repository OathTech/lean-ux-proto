import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Actual fixture scope markers retain every logical journal prefix beside paired packet accounting. The
native driver determines the actual trigger site; a marker creates no ticket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationFixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem enter (cause : CausalSources.Cause) :
    Checked debts locals Safe (CausalScope.enterState Event.scope cause) := by
  intro w a h before
  let event := CausalScope.Event.entered (⟨h.length,cause⟩ : CausalScope.Token Cause)
  obtain ⟨ledger,entry⟩ := before.1
  have kept := entry.append_quiet [Event.scope event]
    (by intro e member; simp only [List.mem_singleton] at member; subst e; rfl)
    (by intro e member position; simp only [List.mem_singleton] at member; subst e; rfl)
  have all := before.2.append (Cuts.singleton before.2.last (accountSafe ledger _ w kept))
  exact ⟨[_],rfl,all,⟨ledger,kept⟩,all⟩

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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationFixture
