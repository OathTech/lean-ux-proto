import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFixture
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationNative

/-! Device configuration carries the independently initialized allocation
companion beside complete packet Entry. Peer creation's freshness is derived
at its native call, while actual removal and identity-triggered sends retain
their counted source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.DeviceConfiguration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver StackOwnership
open AllocatedCarrier ConfigurationReady
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem release (peer : Option PeerId) : Checked debts locals Safe (hooks.peerRelease peer) := by
  apply pair Safe (Source.release peer Safe entrySafe) ?_ (AllocatedFrames.release peer)
  apply NestedPeerRelease.projects_erases old? (hooks_projects.peerRelease peer)
  exact NestedPeerRelease.projects_erases Journal.nonce? (Journal.hooks_projects.peerRelease peer)
    (erasesStatePrefix_lift _)

theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) :=
  pair Safe (LifecycleComplete.remove Safe entrySafe peer) (ConfigurationNative.remove_erases peer)
    (ConfigurationNative.removal peer)

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) :=
  pair Safe (LifecycleComplete.remove_all Safe entrySafe) ConfigurationNative.remove_all_erases
    ConfigurationNative.removal_all

variable (staging : ∀ pid, SourcePassive.Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, SourcePassive.Checked debts locals Safe (keepaliveObserved hooks pid))

omit entrySafe in
include staging in
theorem staged (pid : PeerId) : Checked debts locals Safe (stagingObserved hooks pid) :=
  pair Safe (staging pid) (ConfigurationNative.staging_erases pid) (ConfigurationNative.staging pid)

macro "entry_device_frame" : tactic => `(tactic| first
  | (snapshot_head precomputeStaticStatic; exact SavedFrames.precompute _)
  | (snapshot_head expireCurrentPeerKeypairs; exact KeyFrames.expire _)
  | (snapshot_head clearPeerEndpointSrc; exact EndpointFrames.clear _)
  | (snapshot_head setPort; exact ControlFrames.set_port _)
  | (snapshot_head lookupInterface; exact (lookupInterface_sameWGWorld _).factor StagedEntry.view)
  | (snapshot_head generatePublic; exact (generatePublic_sameWGWorld _).factor StagedEntry.view)
  | entry_allocated_frame)

macro "entry_device_allocation" : tactic => `(tactic| first
  | (rx_retention_head precomputeStaticStatic; exact AllocatedFrames.precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact ConfigurationNative.expire _)
  | (rx_retention_head clearPeerEndpointSrc; exact ConfigurationNative.clear_endpoint _)
  | (rx_retention_head setPort; exact AllocatedFrames.configured (.port _))
  | (rx_retention_head lookupInterface; exact AllocatedFrames.store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head generatePublic; exact AllocatedFrames.store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head setStaticIdentityPrivateKey; exact AllocatedFrames.configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact AllocatedFrames.configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head modifyDev
     apply AllocatedFrames.configuration
     intro initial
     exact modifyDev_configuration_spec (fun t => t = initial) _ (fun _ => rfl))
  | entry_allocation_frame)

macro "entry_device_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head FixtureEffects.runWith
     apply AllocatedFixture.run $safe $entry
     change StatePrefixEnsures (Carrier _ _) _ _ (fun _ => Carrier _ _))
  | (maintenance_head Hooks.peerRelease; exact release $safe $entry _)
  | (maintenance_head removeObserved; exact remove $safe $entry _)
  | (maintenance_head removeAllObserved; exact remove_all $safe $entry)
  | (maintenance_head liftWGPrefix
     apply passive $safe $entry
     · solve | entry_device_frame
     · solve | entry_device_allocation)
  | entry_allocated_step $safe using $entry)

include staging keepalive

theorem key (attrs : DeviceAttrs) : Checked debts locals Safe (configKey hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configKey deviceKeyWith
  repeat' first
    | (maintenance_head configPeers; exact ConfigurationReady.peers Safe entrySafe staging keepalive _)
    | (maintenance_head stagingObserved; exact staged Safe staging _)
    | entry_device_step Safe using entrySafe

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    Checked debts locals Safe (configDeviceUpdate hooks attrs flags) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (maintenance_head configKey; exact key Safe entrySafe staging keepalive _)
    | entry_device_step Safe using entrySafe

theorem device (attrs : DeviceAttrs) : Checked debts locals Safe (configDevice hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configDevice setDeviceWith
  repeat' first
    | (maintenance_head configDeviceUpdate; exact update Safe entrySafe staging keepalive _ _)
    | entry_device_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.DeviceConfiguration
