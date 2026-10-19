import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchivePeerConfig

/-! Configuration shares the native staged-send callbacks with all other
actors. Peer creation and deleting releases carry the concrete source carrier. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins TransmitSecurity Configuration

macro "archive_driver_device_step " : tactic => `(tactic| first
  | (nonce_source_head generatePublic; exact same_world (generatePublic_sameWGWorld _))
  | (nonce_source_head setStaticIdentityPrivateKey
     exact lift _ (configuration (setStaticIdentityPrivateKey_sameConfiguration _)))
  | (nonce_source_head cookiePrecomputeDeviceKeys
     exact lift _ (configuration cookiePrecomputeDeviceKeys_sameConfiguration))
  | (nonce_source_head precomputeStaticStatic; exact lift _ (precompute _))
  | (nonce_source_head expireCurrentPeerKeypairs; exact lift _ (expire _))
  | (nonce_source_head clearPeerEndpointSrc; exact lift _ (clear_endpoint _))
  | (nonce_source_head setPort; exact lift _ (port _))
  | (nonce_source_head peerRemoveAll; exact lift _ (remove_all ))
  | (nonce_source_head peerPut; exact lift _ (peer_put _))
  | (nonce_source_head modifyDev
     apply lift; intro confirmed
     apply modify_device
     intro d; rfl)
  | (nonce_source_head lookupInterface; exact same_world (lookupInterface_sameWGWorld _))
  | archive_driver_config_step )

theorem config_peers (a : DeviceAttrs) :
    Preserves (Driver.configPeers TimestampDriver.hooks a) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold Driver.configPeers devicePeersWith
  repeat' first
    | (nonce_source_head Driver.configPeer; exact config_peer _)
    | archive_driver_device_step

private theorem config_key_with (a : DeviceAttrs)
    (next : WGPrefix TimestampReceipt Int) (safe : Preserves next) :
    Preserves (deviceKeyWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) (fun peer => liftWGPrefix (peerPut peer))
      (fun peer => liftWGPrefix (peerRemove peer)) (fun pid => liftWGPrefix (precomputeStaticStatic pid))
      (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid)) (Driver.stagingObserved TimestampDriver.hooks) next a) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold deviceKeyWith
  repeat' first
    | exact safe
    | archive_driver_device_step

theorem config_key (a : DeviceAttrs) :
    Preserves (Driver.configKey TimestampDriver.hooks a) :=
  config_key_with a _ (config_peers a)

theorem config_device_update (a : DeviceAttrs) (flags : UInt32) :
    Preserves (Driver.configDeviceUpdate TimestampDriver.hooks a flags) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold Driver.configDeviceUpdate deviceUpdateWith
  repeat' first
    | (nonce_source_head Driver.configKey; exact config_key _)
    | archive_driver_device_step

theorem config_device (a : DeviceAttrs) :
    Preserves (Driver.configDevice TimestampDriver.hooks a) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold Driver.configDevice setDeviceWith
  repeat' first
    | (nonce_source_head Driver.configDeviceUpdate; exact config_device_update _ _)
    | archive_driver_device_step

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
