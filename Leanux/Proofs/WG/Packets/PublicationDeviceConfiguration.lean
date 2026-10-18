import Leanux.Proofs.WG.Packets.PublicationDevice
import Leanux.Proofs.WG.Packets.PublicationPeerObserved
import Leanux.Proofs.WG.Origins.JointOwnerDevice

/-! The concrete device command retains publication anchors through private-key
replacement, saved peer iteration and partial errno updates. This concerns
existing packet identities; later current-key validity is not an assumption. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration

private theorem configuration_preserves (a : WG.M α) (frame : SameConfiguration a)
    (history : List RxHistory.Event) : Preserves (Inv history) a := by
  apply preserves_of_configured a
  · apply frame.of_factor
      (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?))
      RxDisposition.nativeRxStore
    intro w
    simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
      RxDisposition.nativeRxStore,Option.map_map,Option.bind_map,Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view
    intro w
    simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
      ConfiguredIdentity.view,ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl

theorem setPort_preserves (port : Nat) (history : List RxHistory.Event) :
    Preserves (Inv history) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearPeerEndpointSrc_preserves _ history)
    | (rx_retention_head socketInit; exact socket_preserves _ (socketInit_sameSocket _) history)
    | publication_removal_step history

private theorem precompute_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (precomputeStaticStatic pid) := by
  apply preserves_of_configured _ ?_ (ConfiguredIdentity.precompute pid) history
  apply SameView.factor (view := OwnerCompletion.geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [branch,requireNotPending]
  repeat' completion_step initial

private theorem expire_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (expireCurrentPeerKeypairs pid) := by
  apply preserves_of_configured _ ?_ (ConfiguredMaintenance.expireCurrentPeerKeypairs_view pid) history
  apply SameView.factor (view := OwnerCompletion.geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold expireCurrentPeerKeypairs handshakeClear handshakeZero resetLastSentHandshake
  simp (config := {zeta := false}) only [requireNotPending,branch,invariant,hiddenClock64]
  repeat' first
    | (allocation_release_lift_from IndexM
       apply hoare_liftIndex
       intro w d table hi hd
       simpa only [OwnerCompletion.geometry,RxCredits.rxView,hd,Option.map_some,Option.bind_some] using hi)
    | completion_step initial

private theorem pubkey_preserves (key : Key) (history : List RxHistory.Event) :
    Preserves (Inv history) (pubkeyLookup key) :=
  (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationHandshakeReceive.«0».Leanux.Proofs.WG.PublicationHandshake.pubkey) key history

macro "publication_device_steps " history:term : tactic => `(tactic| first
  | (rx_retention_head setPeerCmd; exact setPeerCmd_preserves _ $history)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Inv $history))
  | (rx_retention_head peerRemove; exact peerRemove_preserves _ $history)
  | (rx_retention_head peerRemoveAll; exact peerRemoveAll_preserves $history)
  | (rx_retention_head setStaticIdentityPrivateKey
     exact configuration_preserves _ (setStaticIdentityPrivateKey_sameConfiguration _) $history)
  | (rx_retention_head cookiePrecomputeDeviceKeys
     exact configuration_preserves _ cookiePrecomputeDeviceKeys_sameConfiguration $history)
  | (rx_retention_head precomputeStaticStatic; exact precompute_preserves _ $history)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_preserves _ $history)
  | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ $history)
  | (rx_retention_head clearPeerEndpointSrc; exact clearPeerEndpointSrc_preserves _ $history)
  | (rx_retention_head setPort; exact setPort_preserves _ $history)
  | (rx_retention_head pubkeyLookup
     exact pubkey_preserves _ $history)
  | publication_handshake_step $history
  | publication_removal_step $history)

theorem devicePeers_preserves (a : DeviceAttrs) (history : List RxHistory.Event) :
    Preserves (Inv history) (devicePeersSource a) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' publication_device_steps history

theorem deviceKey_preserves (a : DeviceAttrs) (history : List RxHistory.Event) :
    Preserves (Inv history) (deviceKeySource a) := by
  unfold deviceKeySource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head devicePeersSource; exact devicePeers_preserves _ history)
    | publication_device_steps history

theorem deviceUpdate_preserves (a : DeviceAttrs) (flags : UInt32)
    (history : List RxHistory.Event) : Preserves (Inv history) (deviceUpdateSource a flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact deviceKey_preserves _ history)
    | publication_device_steps history

theorem wgSetDevice_preserves (a : DeviceAttrs) (history : List RxHistory.Event) :
    Preserves (Inv history) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Inv history))
    | (rx_retention_head deviceUpdateSource; exact deviceUpdate_preserves _ _ history)
    | publication_device_steps history

end Leanux.Proofs.WG.PublicationFrontier

namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

theorem wgSetDevice (a : DeviceAttrs) :
    Preserves (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix a))) :=
  native_mixed _ _ (JointOwnerDevice.wgSetDevice_checked a)
    (ConfigurationCall.erases (.device a)) (PublicationFrontier.wgSetDevice_preserves a)

end Leanux.Proofs.WG.PublicationJoint
