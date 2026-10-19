import Leanux.Proofs.WG.Packets.PublicationAllowedIps
import Leanux.Proofs.WG.Packets.PublicationTimers
import Leanux.Proofs.WG.Packets.PublicationRemoval

/-! Concrete peer configuration preserves old packet certificates through
creation, removal, allowed-IP edits, saved keepalive writes and nullable final
payment. All attributes and normal errno results remain unrestricted. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration PublicationCompletion
open OwnerCompletion (geometry)

private theorem tail_geometry (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) : SameView geometry (peerTailFinishSource a peer pid ret) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendKeepalive
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.keepalive_geometry) _).wp (fun s => s = initial))
    | (rx_retention_head sendStagedPackets
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) _).wp (fun s => s = initial))
    | completion_step initial

private theorem tail_peers (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) (initial : Option (PeerId → Option (Nat × Key))) :
    Preserves (PeersRetained initial) (peerTailFinishSource a peer pid ret) := by
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendKeepalive
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.keepalive_peers) _ initial)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_peers _ initial)
    | publication_peer_step initial

theorem peerTailFinish_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerTailFinishSource a peer pid ret) :=
  preserves_of_geometry _ (tail_geometry a peer pid ret) (tail_peers a peer pid ret) history

theorem setPeerEndpoint_preserves (pid : PeerId) (endpoint : Endpoint)
    (history : List RxHistory.Event) : Preserves (Inv history) (setPeerEndpoint pid endpoint) :=
  preserves_of_configured _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid endpoint).factor Prod.snd)
    (ConfiguredReceiveLeaves.setPeerEndpoint_view pid endpoint) history

theorem peerConfigTail_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact setAllowedip_preserves _ _ history)
    | (rx_retention_head peerTailFinishSource; exact peerTailFinish_preserves _ _ _ _ history)
    | publication_handshake_step history
    | publication_removal_step history

theorem peerConfigUpdate_preserves (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact peerRemove_preserves _ history)
    | (rx_retention_head setPeerEndpoint; exact setPeerEndpoint_preserves _ _ history)
    | (rx_retention_head removeByPeer; exact removeByPeer_preserves _ history)
    | (rx_retention_head peerConfigTailSource; exact peerConfigTail_preserves _ _ _ history)
    | publication_handshake_step history
    | publication_removal_step history

theorem setPeerCmd_preserves (a : PeerAttrs) (history : List RxHistory.Event) :
    Preserves (Inv history) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact peerCreate_preserves _ _ history)
    | (rx_retention_head peerGet; exact peerGet_preserves _ history)
    | (rx_retention_head pubkeyLookup
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationHandshakeReceive.«0».Leanux.Proofs.WG.PublicationHandshake.pubkey) _ history)
    | (rx_retention_head peerConfigUpdateSource; exact peerConfigUpdate_preserves _ _ _ _ _ history)
    | publication_handshake_step history
    | publication_removal_step history

end Leanux.Proofs.WG.PublicationFrontier
