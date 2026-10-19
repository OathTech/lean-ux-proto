import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTimerCalls
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceCreationFrames

/-! Native receive maintenance preserves positive resident peer references,
including routing acquisition and endpoint/cache updates. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem endpoint (pid : PeerId) (ep : Endpoint) :
    Framing.Preserves Inv (setPeerEndpoint pid ep) := by
  unfold setPeerEndpoint requireNotPending
  simp (config := {zeta := false}) only [branch,pure_bind]
  repeat' first
    | (rx_retention_head endpointEq; exact store (endpointEq_sameStore _ _))
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | peer_reference_timer_step

theorem endpoint_skb (pid : PeerId) (src : SkbSource) :
    Framing.Preserves Inv (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | peer_reference_timer_step

theorem rx_stats (pid : PeerId) (len : Nat) :
    Framing.Preserves Inv (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' peer_reference_timer_step

theorem dishonest (why : Dishonest) :
    Framing.Preserves Inv (WG.dishonest why) := by
  unfold WG.dishonest
  apply modify_device
  intro d
  cases why <;> rfl

theorem route_lookup (root : Option NodeId) (bits key : Nat) :
    Framing.Preserves Inv (WG.lookup root bits key) := by
  unfold WG.lookup
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head swapEndian; exact store (swapEndian_sameWGStore _))
    | (allocation_release_lift_from AipM; exact store ((pinned_const _private.Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess.«0».Leanux.Proofs.WG.Lifetimes.lookup_readAip) (findNode_sameAipStore _ _ _)))
    | (allocation_release_lift_from AipM; exact store ((pinned_const _private.Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess.«0».Leanux.Proofs.WG.Lifetimes.lookup_readAip) (getNode_sameAipStore _)))
    | peer_reference_timer_step

theorem lookup_src (protocol : Nat) (bytes : List UInt8) :
    Framing.Preserves Inv (lookupSrc protocol bytes) := by
  unfold lookupSrc
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.lookup; exact route_lookup _ _ _)
    | peer_reference_timer_step

theorem fresh_rx (pid : PeerId) :
    Framing.Preserves Inv (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | peer_reference_timer_step

macro "peer_reference_receive_step" : tactic => `(tactic| first
  | (rx_retention_head keepKeyFreshRx; exact fresh_rx _)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _)
  | (rx_retention_head timersTraversal; exact traversal _)
  | (rx_retention_head timersDataReceived; exact data_received _)
  | (rx_retention_head updateRxStats; exact rx_stats _ _)
  | (rx_retention_head WG.dishonest; exact dishonest _)
  | (rx_retention_head lookupSrc; exact lookup_src _ _)
  | (rx_retention_head inetEcnDecapsulate; exact store (inetEcnDecapsulate_sameWGStore _ _ _))
  | peer_reference_timer_step)

theorem prepare_rx (pid : PeerId) (pkt : RxPacket) :
    Framing.Preserves Inv (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | rxstack_preserves_join
    | peer_reference_receive_step

theorem finish_rx (pid : PeerId) (ready : Packets.RxReady) :
    Framing.Preserves Inv (Packets.rxFinish pid ready) := by
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_receive_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
