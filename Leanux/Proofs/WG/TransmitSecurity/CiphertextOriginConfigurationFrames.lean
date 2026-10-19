import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginIngressFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceConfigurationLeaves

/-! Configuration retains the TX packet material projection. Keepalive and
staging are handled by their journaled sources because they may allocate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Inv h) action := by
  apply frame
  apply snapshot_wire
  exact same.of_factor (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
    (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,configurationView,
      configurationDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

macro "ciphertext_configuration_frame" : tactic => `(tactic| first
  | (rx_retention_head WG.orM; unfold WG.orM)
  | (rx_retention_head WG.andM; unfold WG.andM)
  | (rx_retention_head peerCreate; exact frame (snapshot_wire (OccurrenceCreation.wire _ _)))
  | (rx_retention_head setAllowedip; exact frame (snapshot_wire (OccurrenceConfiguration.allowedip_set_wire _ _)))
  | (rx_retention_head removeByPeer; exact frame (snapshot_wire (OccurrenceAllowedIps.remove_wire _)))
  | (rx_retention_head peerRemove; exact frame (snapshot_wire (OccurrenceRemoval.remove_wire _)))
  | (rx_retention_head peerRemoveAll; exact frame (snapshot_wire OccurrenceRemoval.remove_all_wire))
  | (rx_retention_head pubkeyLookup; exact frame (snapshot_wire (OccurrenceHandshake.pubkey_lookup_wire _)))
  | (rx_retention_head precomputeStaticStatic; exact frame (snapshot_wire (OccurrenceCreation.precompute_wire _)))
  | (rx_retention_head setStaticIdentityPrivateKey
     exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys
     exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head expireCurrentPeerKeypairs; exact frame (snapshot_wire (OccurrenceKeys.expire_wire _)))
  | (rx_retention_head setPort; exact frame (snapshot_wire (OccurrenceConfiguration.set_port_wire _)))
  | (rx_retention_head socketInit; exact frame (snapshot_wire (OccurrenceConfiguration.socket_wire (socketInit_sameSocket _))))
  | (rx_retention_head clearPeerEndpointSrc; exact frame (snapshot_wire (OccurrenceTimers.clear_endpoint_wire _)))
  | (rx_retention_head lookupInterface; exact store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head setPeerEndpoint; exact frame (snapshot_wire (endpoint_cryptWire _ _)))
  | (rx_retention_head generatePublic; exact store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | ciphertext_handshake_frame)

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins.NativeFrames
