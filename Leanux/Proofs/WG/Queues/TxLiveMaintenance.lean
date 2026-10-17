import Leanux.Proofs.WG.Queues.TxLiveSocket

/-! Actual handshake sends and workqueue flushes retain the TX live frontier.
The bounded recorded and placeholder dispatch paths, partial guards, and final
reference payments remain the native source actions. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

macro "live_handshake_step" : tactic => `(tactic| first
  | (allocation_release_head createInitiation; exact create_initiation _)
  | (allocation_release_head createResponse; exact create_response _)
  | (allocation_release_head addMacToPacket; exact add_mac _ _)
  | (allocation_release_head beginSession; exact begin_session _)
  | (allocation_release_head timersSessionDerived; exact session_derived _)
  | (allocation_release_head timersTraversal; exact traversal _)
  | (allocation_release_head timersAnyAuthenticatedPacketSent; exact authenticated_sent _)
  | (allocation_release_head timersHandshakeInitiated; exact initiated _)
  | (allocation_release_head sendBufferToPeer; exact send_buffer _ _)
  | live_socket_step)

theorem send_initiation (pid : PeerId) : Preserves Ready (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' live_handshake_step

theorem send_response (pid : PeerId) : Preserves Ready (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' live_handshake_step

theorem send_worker (pid : PeerId) : Preserves Ready (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid) (fun _ => peer_put (some pid))

theorem flushed_send (pid : PeerId) : Preserves Ready (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [hidden,invariant]
  repeat' first
    | (allocation_release_head handshakeSendWorker; exact send_worker _)
    | live_socket_step

theorem flushed_clear (pid : PeerId) : Preserves Ready (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (allocation_release_head queuedExpiredZeroKeyMaterial; exact queued_clear _)
    | live_socket_step

theorem drain_send (upTo : Option PeerId) : Preserves Ready (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (allocation_release_head runFlushedSendWork; exact flushed_send _)
    | (allocation_release_head runFlushedClearWork; exact flushed_clear _)
    | live_socket_step

theorem timers_stop (pid : PeerId) : Preserves Ready (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (allocation_release_head drainHandshakeSendWq; exact drain_send _)
    | live_socket_step

theorem remove_after_dead (pid : PeerId) : Preserves Ready (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head keypairsClear; exact keys_clear _)
    | (allocation_release_head timersStop; exact timers_stop _)
    | (allocation_release_head drainHandshakeSendWq; exact drain_send _)
    | live_socket_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
