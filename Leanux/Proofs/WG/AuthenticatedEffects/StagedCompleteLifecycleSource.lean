import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendDrain
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource

/-! Actual removal and shutdown retain forward entry facts and converse
terminal accounting on one ledger at every bind. Purge and reference-release
cuts settle their actual tickets; send/clear drains are fully discharged.
Device reset is a separate caller obligation and is not part of this result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteLifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open CompletePassive Driver
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

macro "complete_lifecycle_step " safe:term " using " accounted:term : tactic => `(tactic| first
  | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ $safe $accounted)
  | (maintenance_head Hooks.stagedPurge; exact CompleteSource.purge _ $safe $accounted)
  | (maintenance_head sendDrainObserved; exact CompleteSendDrain.checked $safe $accounted _)
  | (maintenance_head liftWGPrefix; apply CompletePassive.native $safe $accounted; solve | entry_lifecycle_native)
  | (maintenance_head ForIn.forIn; apply CompleteSendDrain.list $safe $accounted)
  | (maintenance_head Pure.pure; exact pure_checked $safe $accounted _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

/-- Actual timer shutdown and its bounded send/clear drain preserve the same
paired accounting, including every completed cut before a later Stop. -/
theorem timers_stop (pid : PeerId) : Checked debts locals Safe
    (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _
    (fun _ => CompleteCarrier.Carrier debts locals)
  unfold SendExchange.timersStopWith
  repeat' complete_lifecycle_step Safe using accountSafe

theorem after_dead (pid : PeerId) : Checked debts locals Safe
    (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix (sendDrainObserved hooks) hooks.peerRelease pid) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _
    (fun _ => CompleteCarrier.Carrier debts locals)
  unfold StagedDisposal.Lifecycle.afterDeadWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe accountSafe _)
    | complete_lifecycle_step Safe using accountSafe

/-- The actual peer-removal source preserves complete fixed-ticket accounting;
its counted purge and final release use the same successor ledger as Entry. -/
theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _
    (fun _ => CompleteCarrier.Carrier debts locals)
  unfold removeObserved StagedDisposal.Lifecycle.removeWith Configuration.peerRemoveWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe accountSafe _)
    | complete_lifecycle_step Safe using accountSafe

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _
    (fun _ => CompleteCarrier.Carrier debts locals)
  unfold removeAllObserved StagedDisposal.Lifecycle.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe accountSafe _)
    | complete_lifecycle_step Safe using accountSafe

/-- Device down preserves both directions of ticket accounting through actual
purges, key clearing and send/clear drains, without assuming device reset. -/
theorem down : Checked debts locals Safe (downObserved hooks) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _
    (fun _ => CompleteCarrier.Carrier debts locals)
  unfold downObserved StagedDisposal.Lifecycle.downWith StagedDisposal.Lifecycle.stopWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe accountSafe _)
    | complete_lifecycle_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteLifecycle
