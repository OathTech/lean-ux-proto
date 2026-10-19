import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverPeerConfig

/-! Configuration shares the native staged-send callbacks with all other
actors. Peer creation and deleting releases carry the concrete source carrier. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins TransmitSecurity Configuration

macro "responder_driver_device_step " H1:term : tactic => `(tactic| first
  | (nonce_source_head generatePublic; exact same_world (generatePublic_sameWGWorld _))
  | (nonce_source_head setStaticIdentityPrivateKey
     exact lift _ (carrier_configuration (setStaticIdentityPrivateKey_sameConfiguration _)))
  | (nonce_source_head cookiePrecomputeDeviceKeys
     exact lift _ (carrier_configuration cookiePrecomputeDeviceKeys_sameConfiguration))
  | (nonce_source_head precomputeStaticStatic; exact lift _ (carrier_precompute _))
  | (nonce_source_head expireCurrentPeerKeypairs; exact lift _ (carrier_expire _))
  | (nonce_source_head clearPeerEndpointSrc; exact lift _ (carrier_clear_endpoint _))
  | (nonce_source_head setPort; exact lift _ (carrier_port _))
  | (nonce_source_head Driver.removeAllObserved; rw [Driver.removeAll_lift hooks rfl rfl])
  | (nonce_source_head peerRemoveAll; exact lift _ (carrier_remove_all $H1))
  | (nonce_source_head peerPut; exact lift _ (carrier_peer_put _))
  | (nonce_source_head modifyDev
     apply lift; intro confirmed
     apply carrier_modify
     all_goals intro d; rfl)
  | (nonce_source_head lookupInterface; exact same_world (lookupInterface_sameWGWorld _))
  | responder_driver_config_step $H1)

theorem config_peers (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) :
    Preserves (Driver.configPeers hooks a) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold Driver.configPeers devicePeersWith
  repeat' first
    | (nonce_source_head Driver.configPeer; exact config_peer H1 _)
    | responder_driver_device_step H1

private theorem config_key_with (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs)
    (next : WGPrefix Event Int) (safe : Preserves next) :
    Preserves (deviceKeyWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) (fun peer => liftWGPrefix (peerPut peer))
      (fun peer => liftWGPrefix (peerRemove peer)) (fun pid => liftWGPrefix (precomputeStaticStatic pid))
      (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid)) (Driver.stagingObserved hooks) next a) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold deviceKeyWith
  repeat' first
    | exact safe
    | responder_driver_device_step H1

theorem config_key (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) :
    Preserves (Driver.configKey hooks a) := by
  unfold Driver.configKey
  simp only [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  have removal : Driver.removeObserved hooks = fun peer => liftWGPrefix (peerRemove peer) :=
    funext (Driver.remove_lift hooks rfl rfl)
  rw [removal]
  exact config_key_with H1 a _ (config_peers H1 a)

theorem config_device_update (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) (flags : UInt32) :
    Preserves (Driver.configDeviceUpdate hooks a flags) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold Driver.configDeviceUpdate deviceUpdateWith
  repeat' first
    | (nonce_source_head Driver.configKey; exact config_key H1 _)
    | responder_driver_device_step H1

theorem config_device (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) :
    Preserves (Driver.configDevice hooks a) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold Driver.configDevice setDeviceWith
  repeat' first
    | (nonce_source_head Driver.configDeviceUpdate; exact config_device_update H1 _ _)
    | responder_driver_device_step H1

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
