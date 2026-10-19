import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPurgeSource

/-! Original removal and shutdown compose counted purge and reference release
with the actual handshake-work drain. Its callback contract stays explicit
until the drain's own source proof is supplied; reset is not covered here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

omit accountSafe in
theorem list {α β : Type} (xs : List α) (initial : β) (body : α→β→WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StateEnsures (CompleteCarrier.Carrier debts locals) Safe
      (body item acc) (fun _=>CompleteCarrier.Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StateEnsures.forIn xs initial body (fun _=>CompleteCarrier.Carrier debts locals) checked

macro "prefix_lifecycle_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head Hooks.peerRelease; exact Disposal.original _ $safe $entry)
  | (maintenance_head Hooks.stagedPurge; exact Disposal.purge _ $safe $entry)
  | (maintenance_head liftWGPrefix; apply Passive.native $safe $entry; solve | entry_lifecycle_native)
  | (maintenance_head ForIn.forIn; apply list $safe)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (drained : ∀ upTo, Checked debts locals Safe (sendDrainObserved hooks upTo))
include drained

theorem timers_stop (pid : PeerId) : Checked debts locals Safe
    (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold SendExchange.timersStopWith
  repeat' first
    | (maintenance_head sendDrainObserved; exact drained _)
    | prefix_lifecycle_step Safe using accountSafe

theorem after_dead (pid : PeerId) : Checked debts locals Safe
    (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix (sendDrainObserved hooks) hooks.peerRelease pid) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold StagedDisposal.Lifecycle.afterDeadWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe accountSafe drained _)
    | (maintenance_head sendDrainObserved; exact drained _)
    | prefix_lifecycle_step Safe using accountSafe

theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold removeObserved StagedDisposal.Lifecycle.removeWith Configuration.peerRemoveWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe accountSafe drained _)
    | prefix_lifecycle_step Safe using accountSafe

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold removeAllObserved StagedDisposal.Lifecycle.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe accountSafe drained _)
    | prefix_lifecycle_step Safe using accountSafe

theorem down : Checked debts locals Safe (downObserved hooks) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold downObserved StagedDisposal.Lifecycle.downWith StagedDisposal.Lifecycle.stopWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe accountSafe drained _)
    | prefix_lifecycle_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Lifecycle
