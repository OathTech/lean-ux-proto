import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryDeviceConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedFixture
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationNative

/-! Device configuration carries the independently initialized allocation
companion beside paired packet accounting. Peer creation's freshness is derived
at its native call, while actual removal and identity-triggered sends retain
their counted source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceConfiguration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver StackOwnership
open CompleteAllocated CompleteConfigurationReady
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem release (peer : Option PeerId) : Checked debts locals Safe (hooks.peerRelease peer) := by
  apply pair Safe (CompleteSource.original peer Safe accountSafe) ?_ (AllocatedFrames.release peer)
  apply NestedPeerRelease.projects_erases old? (hooks_projects.peerRelease peer)
  exact NestedPeerRelease.projects_erases Journal.nonce? (Journal.hooks_projects.peerRelease peer)
    (erasesStatePrefix_lift _)

theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) :=
  pair Safe (CompleteLifecycle.remove Safe accountSafe peer) (ConfigurationNative.remove_erases peer)
    (ConfigurationNative.removal peer)

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) :=
  pair Safe (CompleteLifecycle.remove_all Safe accountSafe) ConfigurationNative.remove_all_erases
    ConfigurationNative.removal_all

variable (staging : ∀ pid, CompletePassive.Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, CompletePassive.Checked debts locals Safe (keepaliveObserved hooks pid))

omit accountSafe in
include staging in
theorem staged (pid : PeerId) : Checked debts locals Safe (stagingObserved hooks pid) :=
  pair Safe (staging pid) (ConfigurationNative.staging_erases pid) (ConfigurationNative.staging pid)

macro "complete_device_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head FixtureEffects.runWith
     apply CompleteAllocatedFixture.run $safe $entry
     change StatePrefixEnsures (Carrier _ _) _ _ (fun _ => Carrier _ _))
  | (maintenance_head Hooks.peerRelease; exact release $safe $entry _)
  | (maintenance_head removeObserved; exact remove $safe $entry _)
  | (maintenance_head removeAllObserved; exact remove_all $safe $entry)
  | (maintenance_head liftWGPrefix
     apply passive $safe $entry
     · solve | entry_device_frame
     · solve | entry_device_allocation)
  | complete_allocated_step $safe using $entry)

include staging keepalive

theorem key (attrs : DeviceAttrs) : Checked debts locals Safe (configKey hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configKey deviceKeyWith
  repeat' first
    | (maintenance_head configPeers; exact CompleteConfigurationReady.peers Safe accountSafe staging keepalive _)
    | (maintenance_head stagingObserved; exact staged Safe staging _)
    | complete_device_step Safe using accountSafe

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    Checked debts locals Safe (configDeviceUpdate hooks attrs flags) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (maintenance_head configKey; exact key Safe accountSafe staging keepalive _)
    | complete_device_step Safe using accountSafe

theorem device (attrs : DeviceAttrs) : Checked debts locals Safe (configDevice hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configDevice setDeviceWith
  repeat' first
    | (maintenance_head configDeviceUpdate; exact update Safe accountSafe staging keepalive _ _)
    | complete_device_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceConfiguration
