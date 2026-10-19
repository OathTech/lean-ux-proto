import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionTraffic
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialConfigurationFrames
import Leanux.Proofs.WG.Origins.ConfiguredCommand

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Configuration

/-- Native configuration effects from C2 pin
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`. Each field names the corresponding
`Noise.PendingTickets` declaration and carries no initialized/history claim. -/
structure H1ConfigurationFrames : Prop where
  /-- `setPeerCmd_retained`. -/
  peer : ∀ attrs, ProjectedAction view Retained (setPeerCmd attrs)
  /-- `pubkeyLookup_frame`. -/
  pubkey : ∀ key, SameView view (pubkeyLookup key)
  /-- `peerRemove_retained`. -/
  remove : ∀ peer, ProjectedAction view Retained (peerRemove peer)
  /-- `peerRemoveAll_retained`. -/
  removeAll : ProjectedAction view Retained peerRemoveAll
  /-- `precomputeStaticStatic_frame`. -/
  precompute : ∀ pid, SameView view (precomputeStaticStatic pid)
  /-- `expireCurrentPeerKeypairs_frame`. -/
  expire : ∀ pid, SameView view (expireCurrentPeerKeypairs pid)
  /-- `setStaticIdentityPrivateKey_frame`. -/
  identity : ∀ key, SameView view (setStaticIdentityPrivateKey key)
  /-- `cookiePrecomputeDeviceKeys_frame`. -/
  cookies : SameView view cookiePrecomputeDeviceKeys
  /-- `setPort_frame`. -/
  port : ∀ port, SameView view (setPort port)
  /-- `clearPeerEndpointSrc_frame`. -/
  endpoint : ∀ pid, SameView view (clearPeerEndpointSrc pid)

theorem Carrier.config_peer (frames : H1ConfigurationFrames) (attrs : PeerAttrs) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (setPeerCmd attrs) :=
  Carrier.join confirmed (ConfiguredCommand.command attrs) (CurrentSlots.Configuration.command attrs)
    (PendingPromotion.preserves (frames.peer attrs) confirmed)

theorem Carrier.remove (frames : H1ConfigurationFrames) (peer : Option PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (peerRemove peer) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_remove peer)
    (PendingPromotion.preserves (frames.remove peer) confirmed)

theorem Carrier.remove_all (frames : H1ConfigurationFrames) (confirmed : List Nat) :
    Preserves (Carrier confirmed) peerRemoveAll :=
  Carrier.bounds confirmed ResidentMaterial.bounds_remove_all
    (PendingPromotion.preserves frames.removeAll confirmed)

theorem Carrier.staged (quiet : H1PendingQuietFrames) (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (sendStagedPackets pid) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_staging pid)
    (PendingPromotion.preserves (quiet.staging pid) confirmed)

macro "pending_config_native_step " quiet:term "," frames:term "," confirmed:term : tactic => `(tactic| first
  | (rx_retention_head setPeerCmd; exact Carrier.config_peer $frames _ $confirmed)
  | (rx_retention_head pubkeyLookup
     exact Carrier.from_frame (fun labels => Responder.DriverCuts.carrier_frame labels
       (ConfiguredReceive.pubkeyLookup_view _) (Responder.pubkey_native _ labels)) (($frames).pubkey _) $confirmed)
  | (rx_retention_head peerRemove; exact Carrier.remove $frames _ $confirmed)
  | (rx_retention_head peerRemoveAll; exact Carrier.remove_all $frames $confirmed)
  | (rx_retention_head precomputeStaticStatic
     exact Carrier.from_frame (Responder.DriverCuts.carrier_precompute _) (($frames).precompute _) $confirmed)
  | (rx_retention_head expireCurrentPeerKeypairs
     exact Carrier.from_frame (Responder.DriverCuts.carrier_expire _) (($frames).expire _) $confirmed)
  | (rx_retention_head setStaticIdentityPrivateKey
     exact Carrier.from_frame (Responder.DriverCuts.carrier_configuration (setStaticIdentityPrivateKey_sameConfiguration _)) (($frames).identity _) $confirmed)
  | (rx_retention_head cookiePrecomputeDeviceKeys
     exact Carrier.from_frame (Responder.DriverCuts.carrier_configuration cookiePrecomputeDeviceKeys_sameConfiguration) ($frames).cookies $confirmed)
  | (rx_retention_head clearPeerEndpointSrc
     exact Carrier.from_frame (Responder.DriverCuts.carrier_clear_endpoint _) (($frames).endpoint _) $confirmed)
  | (rx_retention_head setPort
     exact Carrier.from_frame (Responder.DriverCuts.carrier_port _) (($frames).port _) $confirmed)
  | (rx_retention_head sendStagedPackets; exact Carrier.staged $quiet _ $confirmed)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Carrier $confirmed))
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Carrier $confirmed))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Carrier $confirmed)
     intro x acc
     change Preserves (Carrier $confirmed) _)
  | pending_carrier_ingress_step (), $confirmed)

theorem Carrier.config_peers (frames : H1ConfigurationFrames)
    (attrs : DeviceAttrs) (confirmed : List Nat) : Preserves (Carrier confirmed) (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' pending_config_native_step (), frames, confirmed

theorem Carrier.config_key (quiet : H1PendingQuietFrames) (frames : H1ConfigurationFrames)
    (attrs : DeviceAttrs) (confirmed : List Nat) : Preserves (Carrier confirmed) (deviceKeySource attrs) := by
  unfold deviceKeySource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head devicePeersSource; exact Carrier.config_peers frames _ confirmed)
    | pending_config_native_step quiet, frames, confirmed

theorem Carrier.config_update (quiet : H1PendingQuietFrames) (frames : H1ConfigurationFrames)
    (attrs : DeviceAttrs) (flags : UInt32) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact Carrier.config_key quiet frames _ confirmed)
    | pending_config_native_step quiet, frames, confirmed

theorem Carrier.config_device (quiet : H1PendingQuietFrames) (frames : H1ConfigurationFrames)
    (attrs : DeviceAttrs) (confirmed : List Nat) : Preserves (Carrier confirmed) (wgSetDevice attrs) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head deviceUpdateSource; exact Carrier.config_update quiet frames _ _ confirmed)
    | pending_config_native_step quiet, frames, confirmed

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
