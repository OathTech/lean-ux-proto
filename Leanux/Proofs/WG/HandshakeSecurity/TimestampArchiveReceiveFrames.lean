import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimerCalls

/-! Native receive maintenance preserves allocation-indexed timestamp history.
Routing borrows may delete dead peers, so these contracts use retention rather
than equality of the entire peer map. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem endpoint (pid : PeerId) (ep : Endpoint) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (setPeerEndpoint pid ep) := by
  unfold setPeerEndpoint requireNotPending
  simp (config := {zeta := false}) only [branch,pure_bind]
  repeat' first
    | (rx_retention_head endpointEq; exact frame_store history _ (endpointEq_sameStore _ _))
    | (rx_retention_head dstCacheReset; exact cache_reset _ history)
    | archive_timer_step history

theorem endpoint_skb (pid : PeerId) (src : SkbSource) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact frame_store history _ (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _ history)
    | archive_timer_step history

theorem rx_stats (pid : PeerId) (len : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' archive_timer_step history

theorem dishonest (why : Dishonest) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (WG.dishonest why) := by
  unfold WG.dishonest
  apply modify_device
  intro d
  cases why <;> rfl

theorem route_lookup (root : Option NodeId) (bits key : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (WG.lookup root bits key) := by
  unfold WG.lookup
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head swapEndian; exact frame_store history _ (swapEndian_sameWGStore _))
    | (allocation_release_lift_from AipM; exact frame_store history _ ((pinned_const _private.Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess.«0».Leanux.Proofs.WG.Lifetimes.lookup_readAip) (findNode_sameAipStore _ _ _)))
    | (allocation_release_lift_from AipM; exact frame_store history _ ((pinned_const _private.Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess.«0».Leanux.Proofs.WG.Lifetimes.lookup_readAip) (getNode_sameAipStore _)))
    | archive_timer_step history

theorem lookup_src (protocol : Nat) (bytes : List UInt8) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (lookupSrc protocol bytes) := by
  unfold lookupSrc
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.lookup; exact route_lookup _ _ _ history)
    | archive_timer_step history

theorem fresh_rx (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _ history)
    | archive_timer_step history

macro "archive_receive_step " history:term : tactic => `(tactic| first
  | (rx_retention_head keepKeyFreshRx; exact fresh_rx _ $history)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _ $history)
  | (rx_retention_head timersTraversal; exact traversal _ $history)
  | (rx_retention_head timersDataReceived; exact data_received _ $history)
  | (rx_retention_head updateRxStats; exact rx_stats _ _ $history)
  | (rx_retention_head WG.dishonest; exact dishonest _ $history)
  | (rx_retention_head lookupSrc; exact lookup_src _ _ $history)
  | (rx_retention_head inetEcnDecapsulate; exact frame_store $history _ (inetEcnDecapsulate_sameWGStore _ _ _))
  | archive_timer_step $history)

theorem prepare_rx (pid : PeerId) (pkt : RxPacket) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | rxstack_preserves_join
    | archive_receive_step history

theorem finish_rx (pid : PeerId) (ready : Packets.RxReady) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Packets.rxFinish pid ready) := by
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp (config := {zeta := false}) only [branch]
  repeat' archive_receive_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
