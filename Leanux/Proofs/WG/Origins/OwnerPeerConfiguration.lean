import Leanux.Proofs.WG.Origins.OwnerAllowedIps
import Leanux.Proofs.WG.Origins.OwnerRemoval
import Leanux.Proofs.WG.Configuration.AllowedIpSource

/-! Native carrier preservation for peer-configuration tails. The contracts
include allocation refusals, nullable payment and all source guards, and state
only normal endpoint preservation. They do not assume positive references. -/
namespace Leanux.Proofs.WG.OwnerPeerConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits Configuration OwnerBounds OwnerControls

theorem setPeerEndpoint_preserves (pid : PeerId) (endpoint : Endpoint) :
    Preserves Carrier (setPeerEndpoint pid endpoint) :=
  OwnerCompletion.preserves_of_frames _
    (Origins.Retaining.of_view (Origins.Retaining.setPeerEndpoint_material pid endpoint))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry)
      pid endpoint)
    (control_keyEffects (project := id) (allowed := NoPromotion) (setPeerEndpoint_control pid endpoint))

theorem sendKeepalive_preserves (pid : PeerId) : Preserves Carrier (sendKeepalive pid) := by
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (allocation_release_head sendStagedPackets; exact OwnerCompletion.sendStagedPackets_preserves _)
    | owner_control_step

theorem peerTailFinish_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) : Preserves Carrier (peerTailFinishSource a peer pid ret) := by
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head sendKeepalive; exact sendKeepalive_preserves _)
    | (allocation_release_head sendStagedPackets; exact OwnerCompletion.sendStagedPackets_preserves _)
    | owner_control_step

theorem peerConfigTail_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) : Preserves Carrier (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (allocation_release_head setAllowedip; exact OwnerAllowedIps.setAllowedip_preserves _ _)
    | (allocation_release_head peerTailFinishSource; exact peerTailFinish_preserves _ _ _ _)
    | owner_control_step

theorem peerConfigUpdate_preserves (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves Carrier (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head peerRemove; exact OwnerRemoval.peerRemove_preserves _)
    | (allocation_release_head setPeerEndpoint; exact setPeerEndpoint_preserves _ _)
    | (allocation_release_head removeByPeer; exact OwnerAllowedIps.removeByPeer_preserves _)
    | (allocation_release_head peerConfigTailSource; exact peerConfigTail_preserves _ _ _)
    | owner_control_step

end Leanux.Proofs.WG.OwnerPeerConfiguration
