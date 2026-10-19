import Leanux.Proofs.WG.Origins.JointOwnerConfiguration
import Leanux.Proofs.WG.Origins.CurrentRemaining
import Leanux.Proofs.WG.Origins.OwnerDevice

/-! The actual device configuration source preserves current identity and
receiving-owner bounds together. The existing lifetime observer carries the
same native endpoint and its complete failed prefixes into owner checks. -/
namespace Leanux.Proofs.WG.JointOwnerDevice
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration CurrentLifecycle CurrentTraffic ConfiguredHandshake OwnerControls
open Queues.RxCredits CurrentDeferred OwnerCompletion JointOwnerConfiguration

private theorem joint {α : Type} (a : WG.M α) (history : List SessionOrigin.Receipt)
    (current : Preserves (CurrentLifecycle.Inv history) a)
    (owner : Preserves OwnerBounds.Carrier a) :
    Preserves (JointOwnerConfiguration.Inv history) a :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerConfiguration.«0».Leanux.Proofs.WG.JointOwnerConfiguration.combine) a history current owner

private theorem socket_owner {α : Type} (a : WG.M α) (frame : SameSocket a) :
    Preserves OwnerBounds.Carrier a := by
  apply OwnerCompletion.preserves_of_frames a
    (Origins.Retaining.of_view (Origins.Retaining.socketControl_material (project := id) _
      (frame.factor WGOwnedView.toWGStoreView)))
  · exact frame.of_factor (fun s : WGOwnedView => OwnerCompletion.geometry {dev := s.dev})
      _ (fun w => by
        simp only [OwnerCompletion.geometry,rxView,socketView,wgOwnedView,wgStoreView,socketDevice,
          Option.map_map,Option.bind_map,Function.comp_def])
  · apply keyEffects_view (allowed := NoPromotion)
    exact frame.of_factor (fun s : WGOwnedView => keyView {dev := s.dev})
      _ (fun w => by
        unfold keyView keyWords currentCells
        simp only [socketView,wgOwnedView,wgStoreView,socketDevice,id,
          Option.map_map,Option.bind_map,Function.comp_def])

private theorem configuration_preserves {α : Type} (a : WG.M α)
    (frame : SameConfiguration a) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) a := by
  have material := Origins.Retaining.of_view (Origins.Retaining.configuration_material
    (project := id) a (frame.factor WGOwnedView.toWGStoreView))
  apply joint a history
  · apply current_preserves a ?_ material history
    exact frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view (fun w => by
        simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
          ConfiguredIdentity.view,ConfiguredIdentity.state,Option.map_map,Function.comp_def]
        rfl)
  · apply OwnerCompletion.preserves_of_frames a material
    · exact frame.of_factor (fun s : WGOwnedView => OwnerCompletion.geometry {dev := s.dev})
        _ (fun w => by
          simp only [OwnerCompletion.geometry,rxView,configurationView,wgOwnedView,wgStoreView,
            configurationDevice,Option.map_map,Option.bind_map,Function.comp_def])
    · apply keyEffects_view (allowed := NoPromotion)
      exact frame.of_factor (fun s : WGOwnedView => keyView {dev := s.dev})
        _ (fun w => by
          unfold keyView keyWords currentCells
          simp only [configurationView,wgOwnedView,wgStoreView,configurationDevice,id,
            Option.map_map,Option.bind_map,Function.comp_def])

private theorem clearEndpoint_owner (pid : PeerId) :
    Preserves OwnerBounds.Carrier (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' owner_control_step

private theorem clearEndpoint_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (clearPeerEndpointSrc pid) := by
  apply joint _ history ?_ (clearEndpoint_owner pid)
  deferred_native_step history

theorem setPort_preserves (port : Nat) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_preserves _ history)
    | (rx_retention_head socketInit
       exact joint _ history
         ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.socketInit_preserves) _ history)
         (socket_owner _ (socketInit_sameSocket _)))
    | (rx_retention_head modifyDev
       apply joint _ history
       · current_lifecycle_step history
       · owner_control_step)
    | joint_configuration_step history

private theorem precompute_owner (pid : PeerId) :
    Preserves OwnerBounds.Carrier (precomputeStaticStatic pid) := by
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [branch,requireNotPending]
  repeat' owner_control_step

private theorem expire_owner (pid : PeerId) :
    Preserves OwnerBounds.Carrier (expireCurrentPeerKeypairs pid) := by
  apply OwnerCompletion.preserves_of_frames _
    (Origins.Retaining.expireCurrentPeerKeypairs_material pid)
  · intro initial
    change Preserves (fun w => OwnerCompletion.geometry w = initial) _
    unfold expireCurrentPeerKeypairs handshakeClear handshakeZero resetLastSentHandshake
    simp (config := {zeta := false}) only [requireNotPending,branch,invariant,hiddenClock64]
    repeat' first
      | (allocation_release_lift_from IndexM
         apply hoare_liftIndex
         intro w d table hi hd
         simpa only [OwnerCompletion.geometry,rxView,hd,Option.map_some,Option.bind_some] using hi)
      | completion_step initial
  · apply keyEffects_view (allowed := NoPromotion)
    exact (Affiliation.expireCurrentPeerKeypairs_view pid).of_factor
      stateKeyView _ keyView_factor

private theorem expire_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (expireCurrentPeerKeypairs pid) :=
  joint _ history
    (current_preserves _ (ConfiguredMaintenance.expireCurrentPeerKeypairs_view pid)
      (Origins.Retaining.expireCurrentPeerKeypairs_material pid) history) (expire_owner pid)

macro "joint_device_step " history:term : tactic => `(tactic| first
  | (rx_retention_head modifyDev
     apply joint _ $history
     · current_lifecycle_step $history
     · owner_control_step)
  | (rx_retention_head setPeerCmd; exact setPeerCmd_preserves _ $history)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (JointOwnerConfiguration.Inv $history))
  | (rx_retention_head peerRemove
     exact joint _ $history (CurrentLifecycle.peerRemove_preserves _ $history)
       (OwnerRemoval.peerRemove_preserves _))
  | (rx_retention_head peerRemoveAll
     exact joint _ $history (CurrentLifecycle.peerRemoveAll_preserves $history)
       OwnerDevice.peerRemoveAll_preserves)
  | (rx_retention_head setStaticIdentityPrivateKey
     exact configuration_preserves _ (setStaticIdentityPrivateKey_sameConfiguration _) $history)
  | (rx_retention_head cookiePrecomputeDeviceKeys
     exact configuration_preserves _ cookiePrecomputeDeviceKeys_sameConfiguration $history)
  | (rx_retention_head precomputeStaticStatic
     exact joint _ $history
       (current_preserves _ (ConfiguredIdentity.precompute _)
         (Origins.Retaining.of_view (Origins.Retaining.precomputeStaticStatic_material _)) $history)
       (precompute_owner _))
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_preserves _ $history)
  | (rx_retention_head sendStagedPackets
     exact joint _ $history (CurrentTraffic.sendStagedPackets_preserves _ $history)
       (OwnerCompletion.sendStagedPackets_preserves _))
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_preserves _ $history)
  | (rx_retention_head setPort; exact setPort_preserves _ $history)
  | joint_configuration_step $history)

theorem devicePeers_preserves (a : DeviceAttrs) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (devicePeersSource a) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' joint_device_step history

theorem deviceKey_preserves (a : DeviceAttrs) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (deviceKeySource a) := by
  unfold deviceKeySource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head devicePeersSource; exact devicePeers_preserves _ history)
    | joint_device_step history

theorem deviceUpdate_preserves (a : DeviceAttrs) (flags : UInt32)
    (history : List SessionOrigin.Receipt) : Preserves (JointOwnerConfiguration.Inv history) (deviceUpdateSource a flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact deviceKey_preserves _ history)
    | joint_device_step history

theorem wgSetDevice_preserves (a : DeviceAttrs) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (JointOwnerConfiguration.Inv history))
    | (rx_retention_head deviceUpdateSource; exact deviceUpdate_preserves _ _ history)
    | joint_device_step history

/-- The actual device lifetime observer carries joint owner/current checks on
its normal endpoint and preserves the checks on every emitted failed prefix. -/
theorem wgSetDevice_checked (a : DeviceAttrs) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix a))) := by
  apply OwnerConfiguration.native_mixed _ _ (ConfigurationCall.erases (.device a))
    (ConfigurationCall.allocation (.device a)) (Origins.Retaining.wgSetDevice_material a)
  intro allocation history
  exact hoare_consequence (wgSetDevice_preserves a history)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

end Leanux.Proofs.WG.JointOwnerDevice
