import Leanux.Proofs.WG.HandshakeSecurity.ResponderPeerConfiguration

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining Configuration

theorem setPort_native (port : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_native _ confirmed)
    | (rx_retention_head socketInit; exact socket_native (socketInit_sameSocket _) confirmed)
    | responder_config_step confirmed

macro "responder_device_steps " H1:term:max confirmed:term:max : tactic => `(tactic| first
  | (rx_retention_head setPeerCmd; exact setPeer_native $H1 _ $confirmed)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (History.Native $confirmed))
  | (rx_retention_head peerRemove; exact remove_native $H1 _ $confirmed)
  | (rx_retention_head peerRemoveAll; exact removeAll_native $H1 $confirmed)
  | (rx_retention_head setStaticIdentityPrivateKey
     exact configuration_native (setStaticIdentityPrivateKey_sameConfiguration _) $confirmed)
  | (rx_retention_head cookiePrecomputeDeviceKeys
     exact configuration_native cookiePrecomputeDeviceKeys_sameConfiguration $confirmed)
  | (rx_retention_head precomputeStaticStatic; exact precompute_native _ $confirmed)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_native _ $confirmed)
  | (rx_retention_head sendStagedPackets; exact staged_native _ $confirmed)
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_native _ $confirmed)
  | (rx_retention_head setPort; exact setPort_native _ $confirmed)
  | (rx_retention_head pubkeyLookup
     exact pubkey_native _ $confirmed)
  | responder_config_step $confirmed)

theorem devicePeers_native (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (devicePeersSource a) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' responder_device_steps H1 confirmed

theorem deviceKey_native (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (deviceKeySource a) := by
  unfold deviceKeySource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head devicePeersSource; exact devicePeers_native H1 _ confirmed)
    | responder_device_steps H1 confirmed

theorem deviceUpdate_native (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) (flags : UInt32)
    (confirmed : List Nat) : Preserves (History.Native confirmed) (deviceUpdateSource a flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact deviceKey_native H1 _ confirmed)
    | responder_device_steps H1 confirmed

theorem wgSetDevice_native (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (History.Native confirmed))
    | (rx_retention_head deviceUpdateSource; exact deviceUpdate_native H1 _ _ confirmed)
    | responder_device_steps H1 confirmed


theorem Joint.wgSetDevice (H1 : H1ResponderCurrentEdges) (a : DeviceAttrs) :
    Joint.Preserves (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix a))) :=
  Joint.from_global _ (PublicationJoint.wgSetDevice a)
    (Global.native_mixed _ _ (ConfigurationCall.erases (.device a)) (wgSetDevice_native H1 a))

end Leanux.Proofs.WG.HandshakeSecurity.Responder
