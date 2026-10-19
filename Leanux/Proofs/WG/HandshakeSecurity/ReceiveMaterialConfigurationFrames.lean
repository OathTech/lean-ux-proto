import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialTraffic
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialConfigurationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfigurationFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceConfigurationLeaves

/-! Configuration and removal preserve conditional allocation certificates for
resident crypted RX packets. Native drains use the same send and clear source frames. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.ConfigurationFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Responder Origins.Retaining AuthenticatedEffects
open HandshakeFrames TimerFrames
open ResidentMaterial (core_of_same lower_frame)
open ResidentMaterial.NativeFrames (lower_owner_geometry lower_slot_fields expire_core)
set_option maxHeartbeats 600000

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Bounded h) action := by
  apply bounded_frame
  · exact TransportConfiguration.configuration_rx action same
  · apply core_of_same
    apply same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
    intro w
    funext kid
    simp only [pool,configurationView,configurationDevice,wgOwnedView,wgStoreView,
      Option.bind_map,Function.comp_def]
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => ResidentMaterial.cursor {dev:=s.dev}) ResidentMaterial.cursor
      (fun w => by simp [ResidentMaterial.cursor,configurationView,configurationDevice,wgOwnedView,wgStoreView,
        Option.map_map,Function.comp_def])

theorem socket_frame {action : WG.M α} (same : SameSocket action) : Preserves (Bounded h) action := by
  apply bounded_frame
  · exact TransportConfiguration.socket_rx action same
  · apply core_of_same
    apply same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
    intro w
    funext kid
    simp only [pool,socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => ResidentMaterial.cursor {dev:=s.dev}) ResidentMaterial.cursor
      (fun w => by simp [ResidentMaterial.cursor,socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

theorem peer_create (key : Key) (psk : Option Key) : Preserves (Bounded h) (peerCreate key psk) := by
  apply bounded_frame (TransportConfiguration.peerCreate_rx key psk)
    (core_of_same (pool_of_material (peerCreate_material key psk)))
  intro bound
  apply lower_frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have metadata := (peerCreate_geometry key psk w v result a b run).2.1
  have next := congrArg (fun m : AllocationMetadata => m.device.map (·.nextKeypair)) metadata
  cases result <;> simpa only [ResidentMaterial.cursor,peerCreateMetadata,allocationMetadata,deviceAllocationMetadata,
    Option.map_map,Function.comp_def] using next

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Bounded h) (setAllowedip pid ip) :=
  bounded_frame (TransportConfiguration.allowedip_rx pid ip)
    (core_of_same (pool_of_material (setAllowedip_material pid ip)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationAllowedIps.«0».Leanux.Proofs.WG.PublicationFrontier.setAllowedip_geometry) pid ip))

theorem remove_ips (pid : PeerId) : Preserves (Bounded h) (removeByPeer pid) :=
  bounded_frame ((PublicationFrontier.removeByPeer_geometry pid).factor Prod.snd)
    (core_of_same (pool_of_material (removeByPeer_material pid)))
    (fun _ => lower_owner_geometry (PublicationFrontier.removeByPeer_geometry pid))

theorem precompute (pid : PeerId) : Preserves (Bounded h) (precomputeStaticStatic pid) :=
  bounded_frame (TransportConfiguration.precompute_rx pid)
    (core_of_same (pool_of_material (precomputeStaticStatic_material pid)))
    (fun _ => lower_slot_fields (CurrentSlots.precomputeStaticStatic_fields pid))

theorem reset_handshake (pid : PeerId) : Preserves (Bounded h) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp only [hiddenClock64]
  repeat' receive_handshake_leaf

theorem peer_get (pid : PeerId) : Preserves (Bounded h) (peerGet pid) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.peerGet_geometry) pid).factor Prod.snd)
    (core_of_same (pool_of_material (peerGet_material pid)))
    (fun _ => ResidentMaterial.lower_metadata (peerGet_metadata pid))

theorem expire (pid : PeerId) : Preserves (Bounded h) (expireCurrentPeerKeypairs pid) := by
  apply bounded_frame (TransportConfiguration.expire_rx pid) (core_of_same (expire_core pid))
  intro bound
  unfold expireCurrentPeerKeypairs requireNotPending
  simp only [branch,invariant]
  repeat' first
    | (allocation_release_head handshakeClear
       unfold handshakeClear handshakeZero
       repeat' resident_lower_step)
    | (allocation_release_head resetLastSentHandshake
       exact lower_slot_fields (CurrentSlots.resetLastSentHandshake_fields _))
    | resident_lower_step

theorem port (port : Nat) : Preserves (Bounded h) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | receive_handshake_frame

theorem drain_send (upTo : Option PeerId) : Preserves (Bounded h) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushed_send _)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _)
    | (rx_retention_head throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b hi run
       cases run)
    | receive_handshake_frame

theorem stop_timers (pid : PeerId) : Preserves (Bounded h) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _)
    | receive_timer_frame

theorem make_dead (pid : PeerId) : Preserves (Bounded h) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact remove_ips _)
    | receive_handshake_frame

theorem remove_after (pid : PeerId) : Preserves (Bounded h) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact keys_clear _)
    | (rx_retention_head timersStop; exact stop_timers _)
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _)
    | receive_handshake_frame

theorem remove (peer : Option PeerId) : Preserves (Bounded h) (peerRemove peer) := by
  unfold peerRemove
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _)
    | receive_handshake_frame

theorem free_ips : Preserves (Bounded h) WG.free := by
  apply bounded_frame (((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationRemoval.«0».Leanux.Proofs.WG.PublicationFrontier.allowedipsFree_geometry).factor Prod.snd))
    (core_of_same (pool_of_material allowedipsFree_material))
  intro bound
  exact lower_slot_fields CurrentSlots.Removal.free_fields

theorem remove_all : Preserves (Bounded h) peerRemoveAll := by
  unfold peerRemoveAll
  simp only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_ips)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _)
    | receive_handshake_frame

macro "receive_configuration_frame" : tactic => `(tactic| first
  | (rx_retention_head peerCreate; exact peer_create _ _)
  | (rx_retention_head setAllowedip; exact allowedip _ _)
  | (rx_retention_head removeByPeer; exact remove_ips _)
  | (rx_retention_head peerRemove; exact remove _)
  | (rx_retention_head peerRemoveAll; exact remove_all)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire _)
  | (rx_retention_head setPort; exact port _)
  | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head lookupInterface; exact bounded_store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head setPeerEndpoint; exact bounded_endpoint _ _)
  | (rx_retention_head generatePublic; exact bounded_store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | receive_handshake_frame)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.ConfigurationFrames
