import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDeferred
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeviceFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem carrier_allowedip (pid : PeerId) (ip : AllowedIpAttrs) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (setAllowedip pid ip) :=
  carrier_frame confirmed (CurrentConfiguration.setAllowedip_view pid ip) (allowedip_native pid ip confirmed)

theorem carrier_remove (H1 : H1ResponderCurrentEdges) (peer : Option PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (peerRemove peer) :=
  carrier_join confirmed (ConfiguredRemoval.remove peer) (remove_native H1 peer confirmed)

theorem carrier_remove_all (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) peerRemoveAll :=
  carrier_join confirmed ConfiguredRemoval.removeAll (removeAll_native H1 confirmed)

theorem carrier_remove_ips (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (removeByPeer pid) :=
  carrier_frame confirmed (ConfiguredIdentity.removeByPeer_view pid) (removeByPeer_native pid confirmed)

theorem carrier_peer_create (key : Key) (psk : Option Key) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (peerCreate key psk) :=
  carrier_join confirmed
    (hoare_consequence (ConfiguredIdentity.peerCreate_spec key psk) (fun _ hi => hi) (fun _ _ hi => hi.1))
    (peerCreate_native key psk confirmed)

theorem carrier_precompute (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (precomputeStaticStatic pid) :=
  carrier_frame confirmed (ConfiguredIdentity.precompute pid) (precompute_native pid confirmed)

theorem carrier_expire (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (expireCurrentPeerKeypairs pid) :=
  carrier_frame confirmed (ConfiguredMaintenance.expireCurrentPeerKeypairs_view pid) (expire_native pid confirmed)

theorem carrier_socket {action : WG.M α} (frame : SameSocket action) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) action := by
  apply carrier_frame confirmed _ (socket_native frame confirmed)
  apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
  intro w
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

theorem carrier_configuration {action : WG.M α} (frame : SameConfiguration action) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) action := by
  apply carrier_frame confirmed _ (configuration_native frame confirmed)
  apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
  intro w
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

theorem carrier_port (port : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact carrier_clear_endpoint _ confirmed)
    | (rx_retention_head socketInit; exact carrier_socket (socketInit_sameSocket _) confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Framing.Preserves (Carrier confirmed) _)
    | responder_carrier_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
