import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfigurationFrames

/-! Actual peer/device netlink and device-open callers transport the shared
RX carrier across key replacement, removal flushes and native keepalive sends. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

macro "transport_config_rx" : tactic => `(tactic| first
  | (snapshot_head WG.orM; unfold WG.orM; transport_native_rx)
  | (snapshot_head peerCreate; exact TransportConfiguration.peerCreate_rx _ _)
  | (snapshot_head setAllowedip; exact TransportConfiguration.allowedip_rx _ _)
  | (snapshot_head removeByPeer; exact (PublicationFrontier.removeByPeer_geometry _).factor Prod.snd)
  | (snapshot_head peerRemove; exact (TransportRemoval.remove_geometry _).factor Prod.snd)
  | (snapshot_head peerRemoveAll; exact TransportRemoval.removeAll_geometry.factor Prod.snd)
  | (snapshot_head pubkeyLookup; exact TransportConfiguration.pubkey_rx _)
  | (snapshot_head precomputeStaticStatic; exact TransportConfiguration.precompute_rx _)
  | (snapshot_head setStaticIdentityPrivateKey
     exact TransportConfiguration.configuration_rx _ (setStaticIdentityPrivateKey_sameConfiguration _))
  | (snapshot_head cookiePrecomputeDeviceKeys
     exact TransportConfiguration.configuration_rx _ cookiePrecomputeDeviceKeys_sameConfiguration)
  | (snapshot_head expireCurrentPeerKeypairs; exact TransportConfiguration.expire_rx _)
  | (snapshot_head setPort; exact TransportConfiguration.port_rx _)
  | (snapshot_head socketInit; exact TransportConfiguration.socket_rx _ (socketInit_sameSocket _))
  | (snapshot_head clearPeerEndpointSrc; exact TransportConfiguration.clearEndpoint_rx _)
  | (snapshot_head lookupInterface; exact (lookupInterface_sameWGWorld _).factor RxDisposition.nativeRxStore)
  | (snapshot_head setPeerEndpoint; exact endpoint_rx _ _)
  | (snapshot_head generatePublic; exact (generatePublic_sameWGWorld _).factor RxDisposition.nativeRxStore)
  | (snapshot_head modifyDev; apply modifyDev_rx <;> intro d <;> rfl)
  | solve | transport_native_rx)

macro "transport_config_step" : tactic => `(tactic| first
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_config_rx)
  | transport_carrier_state_step)

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe extra origin replay (configOut attrs peer ret) := by
  unfold configOut
  repeat' transport_config_step

theorem configTailFinish_safe (h : StagingSafe extra origin replay hooks) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe extra origin replay (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish
  repeat' first
    | (transport_carrier_head configOut; exact configOut_safe _ _ _)
    | (transport_carrier_head stagingObserved; exact staging h _)
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | transport_config_step

theorem configTail_safe (h : StagingSafe extra origin replay hooks) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateSafe extra origin replay (configTail hooks attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (transport_carrier_head configOut; exact configOut_safe _ _ _)
    | (transport_carrier_head configTailFinish; exact configTailFinish_safe h _ _ _ _)
    | transport_config_step

theorem configUpdate_safe (h : StagingSafe extra origin replay hooks) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe extra origin replay (configUpdate hooks attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (transport_carrier_head configOut; exact configOut_safe _ _ _)
    | (transport_carrier_head configTail; exact configTail_safe h _ _ _)
    | transport_config_step

theorem configPeer_safe (h : StagingSafe extra origin replay hooks) (attrs : PeerAttrs) :
    StateSafe extra origin replay (configPeer hooks attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (transport_carrier_head configOut; exact configOut_safe _ _ _)
    | (transport_carrier_head configUpdate; exact configUpdate_safe h _ _ _ _ _)
    | transport_config_step

theorem configPeers_safe (h : StagingSafe extra origin replay hooks) (attrs : DeviceAttrs) :
    StateSafe extra origin replay (configPeers hooks attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (transport_carrier_head configPeer; exact configPeer_safe h _)
    | transport_config_step

theorem configKey_safe (h : StagingSafe extra origin replay hooks) (attrs : DeviceAttrs) :
    StateSafe extra origin replay (configKey hooks attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (transport_carrier_head configPeers; exact configPeers_safe h _)
    | (transport_carrier_head stagingObserved; exact staging h _)
    | transport_config_step

theorem configDeviceUpdate_safe (h : StagingSafe extra origin replay hooks) (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe extra origin replay (configDeviceUpdate hooks attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (transport_carrier_head configKey; exact configKey_safe h _)
    | transport_config_step

theorem configDevice_safe (h : StagingSafe extra origin replay hooks) (attrs : DeviceAttrs) :
    StateSafe extra origin replay (configDevice hooks attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (transport_carrier_head configDeviceUpdate; exact configDeviceUpdate_safe h _ _)
    | transport_config_step

theorem opened (h : StagingSafe extra origin replay hooks) :
    StateSafe extra origin replay (openObserved hooks) := by
  unfold openObserved
  repeat' first
    | (transport_carrier_head stagingObserved; exact staging h _)
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | transport_config_step

theorem up (h : StagingSafe extra origin replay hooks) :
    StateSafe extra origin replay (upObserved hooks) := by
  unfold upObserved
  repeat' first
    | (transport_carrier_head openObserved; exact opened h)
    | transport_config_step


end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
