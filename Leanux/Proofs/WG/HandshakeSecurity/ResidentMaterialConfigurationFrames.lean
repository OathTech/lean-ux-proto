import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTraffic
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceConfigurationLeaves

/-! Configuration and removal preserve allocation-time sending cores for
resident TX packets. Native drains use the same send and clear source frames. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Responder Origins.Retaining
set_option maxHeartbeats 600000

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Inv h) action := by
  apply frame
  · apply PacketOrigins.snapshot_wire
    exact same.of_factor (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,configurationView,
        configurationDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
  · apply core_of_same
    apply same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
    intro w
    funext kid
    simp only [pool,configurationView,configurationDevice,wgOwnedView,wgStoreView,
      Option.bind_map,Function.comp_def]
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => cursor {dev:=s.dev}) cursor
      (fun w => by simp [cursor,configurationView,configurationDevice,wgOwnedView,wgStoreView,
        Option.map_map,Function.comp_def])

theorem socket_frame {action : WG.M α} (same : SameSocket action) : Preserves (Inv h) action := by
  apply frame
  · exact PacketOrigins.snapshot_wire (OccurrenceConfiguration.socket_wire same)
  · apply core_of_same
    apply same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
    intro w
    funext kid
    simp only [pool,socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => cursor {dev:=s.dev}) cursor
      (fun w => by simp [cursor,socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

theorem peer_create (key : Key) (psk : Option Key) : Preserves (Inv h) (peerCreate key psk) := by
  apply frame (PacketOrigins.snapshot_wire (OccurrenceCreation.wire key psk))
    (core_of_same (pool_of_material (peerCreate_material key psk)))
  intro bound
  apply lower_frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have metadata := (peerCreate_geometry key psk w v result a b run).2.1
  have next := congrArg (fun m : AllocationMetadata => m.device.map (·.nextKeypair)) metadata
  cases result <;> simpa only [cursor,peerCreateMetadata,allocationMetadata,deviceAllocationMetadata,
    Option.map_map,Function.comp_def] using next

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Inv h) (setAllowedip pid ip) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceConfiguration.allowedip_set_wire pid ip))
    (core_of_same (pool_of_material (setAllowedip_material pid ip)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationAllowedIps.«0».Leanux.Proofs.WG.PublicationFrontier.setAllowedip_geometry) pid ip))

theorem remove_ips (pid : PeerId) : Preserves (Inv h) (removeByPeer pid) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceAllowedIps.remove_wire pid))
    (core_of_same (pool_of_material (removeByPeer_material pid)))
    (fun _ => lower_owner_geometry (PublicationFrontier.removeByPeer_geometry pid))

theorem precompute (pid : PeerId) : Preserves (Inv h) (precomputeStaticStatic pid) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceCreation.precompute_wire pid))
    (core_of_same (pool_of_material (precomputeStaticStatic_material pid)))
    (fun _ => lower_slot_fields (CurrentSlots.precomputeStaticStatic_fields pid))

theorem reset_handshake (pid : PeerId) : Preserves (Inv h) (resetLastSentHandshake pid) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceCreation.reset_wire pid))
    (core_of_same (pool_of_material (resetLastSentHandshake_material pid)))
    (fun _ => lower_slot_fields (CurrentSlots.resetLastSentHandshake_fields pid))

theorem invalidate_core (kid : KeypairId) : SameView pool (do
    let key ← getKeypair kid
    setKeypair kid {key with sending := {key.sending with isValid := false}}) := by
  intro initial
  apply hoare_bind _ _ (pool_get (fun p => p = initial) kid)
  intro key
  exact hoare_consequence
    (pool_set (fun p => p = initial) kid {key with sending := {key.sending with isValid := false}})
    (fun _ hi => hi) (fun _ _ hi => hi)

theorem expire_core (pid : PeerId) : SameView pool (expireCurrentPeerKeypairs pid) := by
  intro initial
  have invalid (kid : KeypairId) : Preserves (fun w => pool w = initial) (do
      let key ← getKeypair kid
      setKeypair kid {key with sending := {key.sending with isValid := false}}) :=
    (invalidate_core kid).wp (fun p => p = initial)
  have clear : Preserves (fun w => pool w = initial) (handshakeClear pid) :=
    (pool_of_material (handshakeClear_material pid)).wp (fun p => p = initial)
  have reset : Preserves (fun w => pool w = initial) (resetLastSentHandshake pid) :=
    (pool_of_material (resetLastSentHandshake_material pid)).wp (fun p => p = initial)
  have peer : Preserves (fun w => pool w = initial) (getPeer pid) :=
    (pool_of_material (getPeer_material pid)).wp (fun p => p = initial)
  have ambient {α : Type} (action : AmbientM α) :
      Preserves (fun w => pool w = initial) (monadLift action : WG.M α) := hoare_liftAmbient action _
  change Preserves (fun w => pool w = initial) _
  routing_tx_source [expireCurrentPeerKeypairs,requireNotPending,branch,invariant]
    using [invalid,clear,reset,peer,ambient]

theorem expire (pid : PeerId) : Preserves (Inv h) (expireCurrentPeerKeypairs pid) := by
  apply frame (PacketOrigins.snapshot_wire (OccurrenceKeys.expire_wire pid)) (core_of_same (expire_core pid))
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

theorem port (port : Nat) : Preserves (Inv h) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | resident_handshake_frame

theorem drain_send (upTo : Option PeerId) : Preserves (Inv h) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushed_send _)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _)
    | resident_handshake_frame

theorem stop_timers (pid : PeerId) : Preserves (Inv h) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _)
    | resident_timer_frame

theorem make_dead (pid : PeerId) : Preserves (Inv h) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact remove_ips _)
    | resident_handshake_frame

theorem remove_after (pid : PeerId) : Preserves (Inv h) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact keys_clear _)
    | (rx_retention_head timersStop; exact stop_timers _)
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _)
    | resident_handshake_frame

theorem remove (peer : Option PeerId) : Preserves (Inv h) (peerRemove peer) := by
  unfold peerRemove
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _)
    | resident_handshake_frame

theorem free_ips : Preserves (Inv h) WG.free := by
  apply frame (PacketOrigins.snapshot_wire OccurrenceAllowedIps.free_wire)
    (core_of_same (pool_of_material allowedipsFree_material))
  intro bound
  exact lower_slot_fields CurrentSlots.Removal.free_fields

theorem remove_all : Preserves (Inv h) peerRemoveAll := by
  unfold peerRemoveAll
  simp only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_ips)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _)
    | resident_handshake_frame

macro "resident_configuration_frame" : tactic => `(tactic| first
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
  | (rx_retention_head lookupInterface; exact store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
  | (rx_retention_head generatePublic; exact store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | resident_handshake_frame)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Responder

theorem bounds_remove (peer : Option PeerId) : Preserves Bounds (peerRemove peer) :=
  bounds_join (ConfiguredRemoval.remove peer) (CurrentSlots.Removal.remove peer)

theorem bounds_remove_all : Preserves Bounds peerRemoveAll :=
  bounds_join ConfiguredRemoval.removeAll CurrentSlots.Removal.removeAll

macro "resident_configuration_bounds" : tactic => `(tactic| first
  | (rx_retention_head peerRemove; exact bounds_remove _)
  | (rx_retention_head peerRemoveAll; exact bounds_remove_all)
  | (apply bounds_forget; intro labels
     repeat' first
       | (rx_retention_head peerCreate; exact DriverCuts.carrier_peer_create _ _ labels)
       | (rx_retention_head setAllowedip; exact DriverCuts.carrier_allowedip _ _ labels)
       | (rx_retention_head removeByPeer; exact DriverCuts.carrier_remove_ips _ labels)
       | (rx_retention_head precomputeStaticStatic; exact DriverCuts.carrier_precompute _ labels)
       | (rx_retention_head setStaticIdentityPrivateKey; exact DriverCuts.carrier_configuration (setStaticIdentityPrivateKey_sameConfiguration _) labels)
       | (rx_retention_head cookiePrecomputeDeviceKeys; exact DriverCuts.carrier_configuration cookiePrecomputeDeviceKeys_sameConfiguration labels)
       | (rx_retention_head expireCurrentPeerKeypairs; exact DriverCuts.carrier_expire _ labels)
       | (rx_retention_head setPort; exact DriverCuts.carrier_port _ labels)
       | (rx_retention_head socketInit; exact DriverCuts.carrier_socket (socketInit_sameSocket _) labels)
       | (rx_retention_head clearPeerEndpointSrc; exact DriverCuts.carrier_clear_endpoint _ labels)
       | (rx_retention_head lookupInterface; exact DriverCuts.carrier_store ((lookupInterface_sameWGWorld _).factor wgStoreView) labels)
       | (rx_retention_head generatePublic; exact DriverCuts.carrier_store ((generatePublic_sameWGWorld _).factor wgStoreView) labels)
       | resident_bounds_leaf labels
     done))

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
