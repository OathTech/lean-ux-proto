import Leanux.Proofs.WG.Noise.PendingPeerConfigurationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues
open PendingReception

theorem configuration_leaf {α : Type} (action : WG.M α)
    (same : SameConfiguration action) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) action := by
  apply native_view action ?_
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.configuration) same)
    (PendingTickets.frame_configuration action same) seen
  apply same.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
  intro w
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
    ConfiguredIdentity.view,ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

theorem configuration_lookup (key : Key) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (pubkeyLookup key) :=
  native_view _ (ConfiguredReceive.pubkeyLookup_view key)
    (CurrentSlots.Configuration.pubkey_preserves key) (PendingTickets.pubkeyLookup_frame key) seen

theorem configuration_precompute (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (precomputeStaticStatic pid) :=
  native_view _ (ConfiguredIdentity.precompute pid)
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.precomputeStaticStatic_fields pid))
    (PendingTickets.precomputeStaticStatic_frame pid) seen

theorem configuration_expire (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (expireCurrentPeerKeypairs pid) :=
  native_view _ (ConfiguredMaintenance.expireCurrentPeerKeypairs_view pid)
    (CurrentSlots.expireCurrentPeerKeypairs_preserves pid)
    (PendingTickets.expireCurrentPeerKeypairs_frame pid) seen

theorem configuration_clear_endpoint (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (clearPeerEndpointSrc pid) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.clearEndpoint_view) pid)
    (CurrentSlots.Device.clearEndpoint pid) (PendingTickets.clearPeerEndpointSrc_frame pid) seen

theorem configuration_port (port : Nat) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact configuration_clear_endpoint _ seen)
    | (rx_retention_head socketInit; exact native_socket _ (socketInit_sameSocket _) seen)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => NativeInv w seen)
       intro x acc
       change Preserves (fun w => NativeInv w seen) _)
    | pending_native_step seen

macro "pending_device_config_step " seen:term : tactic => `(tactic| first
  | (rx_retention_head setPeerCmd; exact peer_configuration _ $seen)
  | (rx_retention_head pubkeyLookup; exact configuration_lookup _ $seen)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => NativeInv w $seen))
  | (rx_retention_head peerPut; exact pay _ $seen)
  | (rx_retention_head peerRemove; exact remove _ $seen)
  | (rx_retention_head peerRemoveAll; exact remove_all $seen)
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_leaf _ (setStaticIdentityPrivateKey_sameConfiguration _) $seen)
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_leaf _ cookiePrecomputeDeviceKeys_sameConfiguration $seen)
  | (rx_retention_head precomputeStaticStatic; exact configuration_precompute _ $seen)
  | (rx_retention_head expireCurrentPeerKeypairs; exact configuration_expire _ $seen)
  | (rx_retention_head sendStagedPackets; exact staged _ $seen)
  | (rx_retention_head clearPeerEndpointSrc; exact configuration_clear_endpoint _ $seen)
  | (rx_retention_head setPort; exact configuration_port _ $seen)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun w => NativeInv w $seen)
     intro x acc
     change Preserves (fun w => NativeInv w $seen) _)
  | pending_native_step $seen)


end Leanux.Proofs.WG.Noise.PendingSession
