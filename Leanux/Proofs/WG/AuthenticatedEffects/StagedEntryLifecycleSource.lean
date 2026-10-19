import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRoutingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPurgeSource

/-! Original removal and shutdown compose counted purge and reference release
with the actual handshake-work drain. Its callback contract stays explicit
until the drain's own source proof is supplied; reset is not covered here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.LifecycleSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open SourcePassive Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem list {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StatePrefixEnsures (Source.Carrier debts locals) Safe
      (body item acc) (fun _ => Source.Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => Source.Carrier debts locals) Safe
    (fun _ h w _ before => by obtain ⟨ledger,entry⟩ := before; exact entrySafe ledger h w entry) checked

macro "entry_lifecycle_native" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try simp (config := {zeta := false}) only [requireNotPending,pure_bind]
  repeat' first
    | (rx_retention_head branch; exact (TimerFrames.branch_frame _ _).wp (· = initial))
    | (rx_retention_head peerMakeDead; exact (RoutingFrames.make_dead _).wp (· = initial))
    | (rx_retention_head WG.free; exact RoutingFrames.free.wp (· = initial))
    | (rx_retention_head keypairsClear; exact (KeyFrames.clear_keys _).wp (· = initial))
    | (rx_retention_head handshakeClear; exact (KeyFrames.clear _).wp (· = initial))
    | (rx_retention_head resetLastSentHandshake; exact (ControlFrames.reset_handshake _).wp (· = initial))
    | (rx_retention_head delTimer; exact (TimerFrames.delete _ _).wp (· = initial))
    | (rx_retention_head unsupported; unfold unsupported; exact hoare_liftAmbient _ _)
    | entry_control_step initial))

macro "entry_lifecycle_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head Hooks.peerRelease; exact Source.release _ $safe $entry)
  | (maintenance_head Hooks.stagedPurge; exact Purge.checked _ $safe $entry)
  | (maintenance_head liftWGPrefix; apply SourcePassive.native $safe $entry; solve | entry_lifecycle_native)
  | (maintenance_head ForIn.forIn; apply list $safe $entry)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => Source.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (drained : ∀ upTo, Checked debts locals Safe (sendDrainObserved hooks upTo))
include drained

theorem timers_stop (pid : PeerId) : Checked debts locals Safe
    (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold SendExchange.timersStopWith
  repeat' first
    | (maintenance_head sendDrainObserved; exact drained _)
    | entry_lifecycle_step Safe using entrySafe

theorem after_dead (pid : PeerId) : Checked debts locals Safe
    (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix (sendDrainObserved hooks) hooks.peerRelease pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold StagedDisposal.Lifecycle.afterDeadWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe entrySafe drained _)
    | (maintenance_head sendDrainObserved; exact drained _)
    | entry_lifecycle_step Safe using entrySafe

theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold removeObserved StagedDisposal.Lifecycle.removeWith Configuration.peerRemoveWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe entrySafe drained _)
    | entry_lifecycle_step Safe using entrySafe

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold removeAllObserved StagedDisposal.Lifecycle.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (maintenance_head StagedDisposal.Lifecycle.afterDeadWith; exact after_dead Safe entrySafe drained _)
    | entry_lifecycle_step Safe using entrySafe

theorem down : Checked debts locals Safe (downObserved hooks) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold downObserved StagedDisposal.Lifecycle.downWith StagedDisposal.Lifecycle.stopWith
  repeat' first
    | (maintenance_head SendExchange.timersStopWith; exact timers_stop Safe entrySafe drained _)
    | entry_lifecycle_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.LifecycleSource
