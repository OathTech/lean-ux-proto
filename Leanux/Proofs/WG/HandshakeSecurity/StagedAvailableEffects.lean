import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableNative
import Leanux.Proofs.WG.TransmitSecurity.StagedTimerOriginFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedNativeSupportFrames
import Leanux.Proofs.WG.Queues.HolderStopPhysical

/-! Native metadata, timer, protocol-send and key-clearing paths preserve live
staged birth credits. No staging or keepalive allocator is framed here. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem epoch_rx_ring {action : WG.M α} (same : SameView RxRing.nativeCell action) :
    SameView Packets.epoch action :=
  same.of_factor (fun cell => cell.map Prod.fst) Packets.epoch
    (fun _ => by simp only [RxRing.nativeCell,Packets.epoch,Option.map_map,Function.comp_def])

theorem Native.initiation (msg : List UInt8) : Preserves (Inv h) (consumeInitiation msg) :=
  frame (epoch_rx_ring (RxRing.consumeInitiation_cell msg)) (Staged.initiation msg)

theorem Native.response (msg : List UInt8) : Preserves (Inv h) (consumeResponse msg) :=
  frame (epoch_rx_ring (RxRing.consumeResponse_cell msg)) (Staged.response msg)

theorem Native.session (pid : PeerId) : Preserves (Inv h) (beginSession pid) :=
  frame (epoch_rx_ring (RxRing.beginSession_cell pid)) (Staged.session pid)

theorem Native.confirm (pid : PeerId) (kid : KeypairId) : Preserves (Inv h) (receivedWithKeypair pid kid) :=
  frame (epoch_rx_ring (RxRing.receivedWithKeypair_cell pid kid)) (Staged.confirm pid kid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem exact_ring {action : WG.M α} (epoch : SameView RxRing.nativeCell action)
    (queues : SameView stagedAt action) : Preserves (Inv h) action :=
  frame (epoch_rx_ring epoch) (Staged.of_view _ queues)

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    Preserves (Inv h) (armTimer pid timer delay jc) :=
  exact_ring (RxRing.armTimer_cell pid timer delay jc) (Exact.arm pid timer delay jc)

theorem delete_timer (pid : PeerId) (timer : PeerTimer) : Preserves (Inv h) (delTimer pid timer) :=
  exact_ring (RxRing.delTimer_cell pid timer) (Exact.delete_timer pid timer)

theorem timer_guard (pid : PeerId) : Preserves (Inv h) (modPeerTimerGuard pid) :=
  exact_ring (RxRing.modPeerTimerGuard_cell pid) (Exact.timer_guard pid)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Inv h) (modPeerTimer site pid timer delay) :=
  exact_ring (RxRing.modPeerTimer_cell site pid timer delay) (Exact.modify_timer site pid timer delay)

theorem modTimer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Inv h) (modPeerTimer site pid timer delay) :=
  modify_timer site pid timer delay

theorem data_sent (pid : PeerId) : Preserves (Inv h) (timersDataSent pid) :=
  exact_ring (RxRing.timersDataSent_cell pid) (Exact.data_sent pid)

theorem data_received (pid : PeerId) : Preserves (Inv h) (timersDataReceived pid) :=
  exact_ring (RxRing.timersDataReceived_cell pid) (Exact.data_received pid)

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Inv h) (timersHandshakeComplete pid site) :=
  exact_ring (RxRing.timersHandshakeComplete_cell pid site) (Exact.handshake_complete pid site)

theorem session_derived (pid : PeerId) : Preserves (Inv h) (timersSessionDerived pid) :=
  exact_ring (RxRing.timersSessionDerived_cell pid) (Exact.session_derived pid)

theorem traversal (pid : PeerId) : Preserves (Inv h) (timersTraversal pid) :=
  exact_ring (RxRing.timersTraversal_cell pid) (Exact.traversal pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem endpoint (pid : PeerId) (e : Endpoint) : Preserves (Inv h) (setPeerEndpoint pid e) :=
  exact_ring (RxRing.setPeerEndpoint_cell pid e) (Exact.endpoint pid e)

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : Preserves (Inv h) (sendBufferToPeer pid bytes) :=
  exact_ring (RxRing.sendBufferToPeer_cell pid bytes) (Exact.send_buffer pid bytes)

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves (Inv h) (sendSkbToPeer pid bytes ds) :=
  exact_ring (RxRing.sendSkbToPeer_cell pid bytes ds) (Exact.sendSkbToPeer_staged pid bytes ds)

theorem create_initiation (pid : PeerId) : Preserves (Inv h) (createInitiation pid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceKeys.create_initiation_wire pid).factor Prod.fst))
    (Staged.create_initiation pid)

theorem create_response (pid : PeerId) : Preserves (Inv h) (createResponse pid) :=
  frame (epoch_rx_ring (RxRing.createResponse_cell pid)) (Staged.create_response pid)

theorem add_mac (pid : PeerId) (msg : List UInt8) : Preserves (Inv h) (addMacToPacket pid msg) :=
  frame (epoch_rx_ring (RxRing.addMacToPacket_cell pid msg)) (Staged.add_mac pid msg)

theorem cookie_consume (msg : List UInt8) : Preserves (Inv h) (cookieMessageConsume msg) :=
  frame (epoch_rx_ring (RxRing.cookieMessageConsume_cell msg)) (Staged.cookie_consume msg)

theorem cookie {action : WG.M α} (same : SameCookie action) : Preserves (Inv h) action := by
  apply frame (epoch_rx_ring (RxRing.cookie_native_frame same))
  apply Staged.of_view
  apply same.of_factor (fun s : WGOwnedView => fun pid =>
    (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.staged)) stagedAt
  intro w
  simp only [cookieView,wgOwnedView,wgStoreView,cookieDevice,Option.bind_map,Function.comp_def]
  rfl

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Inv h) (sendHandshakeCookie msg src) := by
  apply frame (epoch_rx_ring (RxRing.sendHandshakeCookie_cell msg src))
  apply Staged.of_view
  apply (Cookies.sendHandshakeCookie_frame msg src).of_factor
    (fun s : Option Device × Nat × Nat => fun pid =>
      (s.1.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.staged)) stagedAt
  intro w
  simp only [Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,
    Option.bind_map,Function.comp_def]
  rfl

theorem endpoint_from_skb (pid : PeerId) (src : SkbSource) :
    Preserves (Inv h) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem clear_endpoint (pid : PeerId) : Preserves (Inv h) (clearPeerEndpointSrc pid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceTimers.clear_endpoint_wire pid).factor Prod.fst))
    (Staged.of_view _ (Exact.clear_endpoint pid))

theorem initiated (pid : PeerId) : Preserves (Inv h) (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Inv h))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (Inv h))
    | (rx_retention_head modPeerTimerGuard; exact Native.timer_guard _)
    | (rx_retention_head armTimer; exact Native.arm _ _ _ _)
    | rx_retention_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

macro "staged_available_native" : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply Native.update_peer_bind
     · intro p; exact ⟨rfl,rfl⟩
     intro x)
  | (receive_update_head setPeer; apply Native.update_peer; intro p; exact ⟨rfl,rfl⟩)
  | (rx_retention_head getPeer; exact Native.read_peer _)
  | (rx_retention_head getKeypair; exact Native.read_key _)
  | (rx_retention_head getDev; exact Native.store getDev_sameWGStore)
  | (rx_retention_head modifyDev; apply Native.modify_device <;> intro d <;> rfl)
  | (rx_retention_head peerGet; exact Native.peer_get _)
  | (rx_retention_head peerPut; exact Native.peer_put _)
  | (rx_retention_head createResponse; exact Native.create_response _)
  | (rx_retention_head createInitiation; exact Native.create_initiation _)
  | (rx_retention_head addMacToPacket; exact Native.add_mac _ _)
  | (rx_retention_head sendBufferToPeer; exact Native.send_buffer _ _)
  | (rx_retention_head setPeerEndpointFromSkb; exact Native.endpoint_from_skb _ _)
  | (rx_retention_head timersHandshakeComplete; exact Native.handshake_complete _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact Native.delete_timer _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact Native.delete_timer _ _)
  | (rx_retention_head sendHandshakeCookie; exact Native.cookie_reply _ _)
  | (rx_retention_head cookieMessageConsume; exact Native.cookie_consume _)
  | (rx_retention_head Cookies.loadPhase; exact Native.store Cookies.loadPhase_sameStore)
  | (rx_retention_head cookieValidatePacket; exact Native.cookie (cookieValidatePacket_sameCookie _ _ _))
  | (rx_retention_head WG.andM; unfold WG.andM)
  | (rx_retention_head WG.orM; unfold WG.orM)
  | (rx_retention_head hiddenClock64; unfold hiddenClock64)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp _)
  | (rx_retention_head branchCmp; unfold branchCmp; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; unfold branch; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head hidden | rx_retention_head invariant | rx_retention_head unsupported | rx_retention_head getAmbient
     first | unfold hidden | unfold invariant | unfold unsupported | unfold getAmbient
     exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem native_clear_keys (pid : PeerId) : Preserves (Inv h) (keypairsClear pid) :=
  frame (epoch_rx_ring (RxCredits.HolderStopPhysical.keys_cell pid)) (Staged.clear_keys pid)

theorem native_clear_handshake (pid : PeerId) : Preserves (Inv h) (handshakeClear pid) :=
  frame (epoch_rx_ring (RxCredits.HolderStopPhysical.handshake_cell pid)) (Staged.clear pid)

theorem native_flushed_clear (pid : PeerId) : Preserves (Inv h) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork queuedExpiredZeroKeyMaterial
  simp only [hidden]
  repeat' first
    | (rx_retention_head handshakeClear; exact native_clear_handshake _)
    | (rx_retention_head keypairsClear; exact native_clear_keys _)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

theorem expired_zero (pid : PeerId) : Preserves (Inv h) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp only [peekQueuedUnit,recordQueued]
  repeat' staged_available_native

theorem fresh_send (pid : PeerId) : Preserves (Inv h) (keepKeyFresh pid) := by
  unfold keepKeyFresh
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
