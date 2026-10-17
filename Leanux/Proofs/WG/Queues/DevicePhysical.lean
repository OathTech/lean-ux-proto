import Leanux.Proofs.WG.Queues.ConfigurationPhysical

/-! The original complete device configuration preserves its exact epoch and
physical receive ring. Optional physical initialization is transported from
input, never supplied as a conclusion premise or inferred from funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open RxRing ConfigurationPhysical Leanux.Proofs.WG.Configuration

private theorem configuration_cell {action : WG.M α} (same : SameConfiguration action) :
    SameView nativeCell action :=
  same.of_factor (fun s : WGOwnedView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) nativeCell
    (fun w => by simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,nativeCell,Option.map_map,Function.comp_def])

private theorem socket_cell {action : WG.M α} (same : SameSocket action) :
    SameView nativeCell action :=
  same.of_factor (fun s : WGOwnedView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) nativeCell
    (fun w => by simp only [socketView,socketDevice,wgOwnedView,wgStoreView,nativeCell,Option.map_map,Function.comp_def])

private theorem clearEndpoint_cell (pid : PeerId) : SameView nativeCell (clearPeerEndpointSrc pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimerPhysical.endpoint_cell) pid

theorem port_cell (port : Nat) : SameView nativeCell (setPort port) := by
  have socket := fun port => socket_cell (socketInit_sameSocket port)
  ring_cell_source [setPort] using [clearEndpoint_cell,socket]

theorem peers_cell (attrs : DeviceAttrs) : SameView nativeCell (devicePeersSource attrs) := by
  ring_cell_source [devicePeersSource] using [command_cell]

private theorem precompute_cell (pid : PeerId) : SameView nativeCell (precomputeStaticStatic pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.ConfigurationPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical.precompute_cell) pid

private theorem expire_cell (pid : PeerId) : SameView nativeCell (expireCurrentPeerKeypairs pid) := by
  ring_cell_source [expireCurrentPeerKeypairs] using
    [requireNotPending_cell,HolderStopPhysical.handshake_cell,HolderStopPhysical.reset_cell,setKeypair_cell]

private theorem keyFinish_cell (key : Key) : SameView nativeCell
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  have identity := fun key => configuration_cell (setStaticIdentityPrivateKey_sameConfiguration key)
  have cookies := configuration_cell cookiePrecomputeDeviceKeys_sameConfiguration
  ring_cell_source [_private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish]
    using [identity,cookies,precompute_cell,expire_cell,sendStagedPackets_cell]

private theorem keyConflict_cell (key : Key) : SameView nativeCell
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  ring_cell_source [_private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict]
    using [pubkeyLookup_cell,peerPut_cell,remove_cell]

private theorem keyChanged_cell (key : Key) : SameView nativeCell
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  have generate (key : Key) : SameView nativeCell (generatePublic key) :=
    (generatePublic_sameWGWorld key).factor nativeCell
  ring_cell_source [_private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged]
    using [generate,keyFinish_cell,keyConflict_cell]

theorem key_cell (attrs : DeviceAttrs) : SameView nativeCell (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  ring_cell_source [] using [keyChanged_cell,peers_cell]

theorem update_cell (attrs : DeviceAttrs) (flags : UInt32) : SameView nativeCell (deviceUpdateSource attrs flags) := by
  ring_cell_source [deviceUpdateSource] using [key_cell,port_cell,clearEndpoint_cell,removeAll_cell]

/-- All actual normal success and errno paths retain the same native cell. -/
theorem device_cell (attrs : DeviceAttrs) : SameView nativeCell (wgSetDevice attrs) := by
  have lookup (spec : DeviceRef) : SameView nativeCell (lookupInterface spec) :=
    (lookupInterface_sameWGWorld spec).factor nativeCell
  rw [←wgSetDevice_source]
  ring_cell_source [wgSetDeviceSource] using [lookup,update_cell]

theorem device_physical (attrs : DeviceAttrs) :
    Preserves HolderDeviceCreate.OptionalPhysical (wgSetDevice attrs) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.ConfigurationPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical.optional) (device_cell attrs)

/-- Funding, structural/configured identity, and physical initialization refer
to the same actual native execution; no endpoint component is assumed. -/
theorem device_entry (attrs : DeviceAttrs) :
    Preserves (fun w => DeviceBoundary.Entry cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) (wgSetDevice attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (DeviceStages.device attrs) w a result v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (device_physical attrs) w a result v b hi.2 run⟩

end Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical
