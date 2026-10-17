import Leanux.Proofs.WG.Queues.TxLiveHandshake
import Leanux.Proofs.WG.Queues.SlotConfiguration

/-! Native peer configuration preserves the live encryption-ring frontier.
Fresh peer allocation, deleting payments and real staged/keepalive sends are
composed at their original positions; normal errno returns remain included. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

private theorem aip_ready (action : AipM α) : Preserves Ready (liftAip action) := by
  apply hoare_liftAip
  intro w d table hi hd
  simpa only [Ready,Inv,Physical,hd,Option.some.injEq,forall_eq'] using hi

private theorem list_add (pid : PeerId) (node : NodeId) : Preserves Ready (listAddTail pid node) := by
  unfold listAddTail
  repeat' live_socket_step

macro "live_aip_step" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip_ready _)
  | (rx_retention_head liftAip; exact aip_ready _)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | live_socket_step)

theorem allowedip_add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves Ready (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact list_add _ _)
    | (rx_retention_head listDel
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveRemoval.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.list_delete) _)
    | live_aip_step

theorem allowedip_insert (family addr cidr : Nat) (pid : PeerId) : Preserves Ready (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact allowedip_add _ _ _ _ _)
    | live_aip_step

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves Ready (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact allowedip_insert _ _ _ _)
    | live_aip_step

theorem precompute (pid : PeerId) : Preserves Ready (precomputeStaticStatic pid) := by
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' live_socket_step

private theorem handshake_init (pid : PeerId) (psk : Option Key) : Preserves Ready (handshakeInit pid psk) := by
  unfold handshakeInit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_word _ _)
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | live_socket_step

theorem peer_create (key : Key) (psk : Option Key) : Preserves Ready (peerCreate key psk) := by
  unfold peerCreate resetLastSentHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,hiddenClock64]
  repeat' first
    | (rx_retention_head dstCacheReset
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveSocket.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.cache_reset) _)
    | (rx_retention_head handshakeInit; exact handshake_init _ _)
    | live_socket_step

theorem peer_finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves Ready (peerTailFinishSource a peer pid ret) := by
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact send _)
    | live_socket_step

theorem peer_tail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves Ready (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact allowedip_set _ _)
    | (rx_retention_head peerTailFinishSource; exact peer_finish _ _ _ _)
    | live_socket_step

theorem peer_update (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves Ready (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact remove_peer _)
    | (rx_retention_head setPeerEndpoint
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveRxCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveRx.endpoint_ready) _ _)
    | (rx_retention_head removeByPeer; exact remove_allowedips _)
    | (rx_retention_head peerConfigTailSource; exact peer_tail _ _ _)
    | live_socket_step

theorem set_peer (attrs : PeerAttrs) : Preserves Ready (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact peer_create _ _)
    | (rx_retention_head peerConfigUpdateSource; exact peer_update _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
    | live_socket_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
