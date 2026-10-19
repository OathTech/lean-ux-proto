import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastSocket

/-! Actual handshake sends, queued drains and timer shutdown preserve historical
encryption exclusion. Callback scheduling and final reference payments retain
the native source order, including refusals and Stops. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Maintenance
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxDisposition Keys Socket
set_option maxHeartbeats 600000

macro "encryption_past_handshake_step" : tactic => `(tactic| first
  | (allocation_release_head sendKeepalive; exact keepalive _)
  | (allocation_release_head createInitiation; exact create_initiation _)
  | (allocation_release_head createResponse; exact create_response _)
  | (allocation_release_head addMacToPacket; exact add_mac _ _)
  | (allocation_release_head beginSession; exact begin_session _)
  | (allocation_release_head timersSessionDerived; exact ready_frame (LiveFrontier.session_derived _) (EncryptionPast.session_derived _))
  | (allocation_release_head timersTraversal; exact ready_frame (LiveFrontier.traversal _) (EncryptionPast.traversal _))
  | (allocation_release_head timersAnyAuthenticatedPacketSent; exact ready_frame (LiveFrontier.authenticated_sent _) (EncryptionPast.del_timer _ _))
  | (allocation_release_head timersHandshakeInitiated; exact ready_frame (LiveFrontier.initiated _) (EncryptionPast.initiated _))
  | (allocation_release_head sendBufferToPeer; exact send_buffer _ _)
  | (allocation_release_head delTimer; exact ready_frame (LiveFrontier.del _ _) (del_timer _ _))
  | encryption_past_socket_step)

theorem send_initiation (pid : PeerId) : Preserves (Ready past active) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' encryption_past_handshake_step

theorem send_response (pid : PeerId) : Preserves (Ready past active) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' encryption_past_handshake_step

theorem send_worker (pid : PeerId) : Preserves (Ready past active) (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid) (fun _ => ready_frame (LiveFrontier.peer_put (some pid)) (peer_put (some pid)))

theorem flushed_send (pid : PeerId) : Preserves (Ready past active) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [hidden,invariant]
  repeat' first
    | (allocation_release_head handshakeSendWorker; exact send_worker _)
    | encryption_past_handshake_step

theorem flushed_clear (pid : PeerId) : Preserves (Ready past active) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (allocation_release_head queuedExpiredZeroKeyMaterial; exact queued_clear _)
    | encryption_past_handshake_step

theorem drain_send (upTo : Option PeerId) : Preserves (Ready past active) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (allocation_release_head runFlushedSendWork; exact flushed_send _)
    | (allocation_release_head runFlushedClearWork; exact flushed_clear _)
    | encryption_past_handshake_step

theorem timers_stop (pid : PeerId) : Preserves (Ready past active) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (allocation_release_head drainHandshakeSendWq; exact drain_send _)
    | encryption_past_handshake_step

theorem remove_after_dead (pid : PeerId) : Preserves (Ready past active) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head keypairsClear; exact keys_clear _)
    | (allocation_release_head timersStop; exact timers_stop _)
    | (allocation_release_head drainHandshakeSendWq; exact drain_send _)
    | encryption_past_handshake_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Maintenance
