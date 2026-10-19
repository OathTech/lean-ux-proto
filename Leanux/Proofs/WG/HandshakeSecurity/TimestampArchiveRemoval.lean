import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveConfigFrames

/-! Removing peers may run queued handshake work. Every native callback keeps
the archive, which retains the allocation history after the peer disappears. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem drain_work (upTo : Option PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushed_send _ history)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _ history)
    | archive_traffic_step history

theorem stop_timers (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact del_timer _ _ history)
    | (rx_retention_head drainHandshakeSendWq; exact drain_work _ history)
    | archive_traffic_step history

theorem make_dead (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact remove_ips _ history)
    | archive_traffic_step history

theorem after_dead (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact clear_keys _ history)
    | (rx_retention_head timersStop; exact stop_timers _ history)
    | (rx_retention_head drainHandshakeSendWq; exact drain_work _ history)
    | archive_traffic_step history

theorem remove (peer : Option PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _ history)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _ history)
    | archive_traffic_step history

theorem remove_all (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_ips history)
    | (rx_retention_head peerMakeDead; exact make_dead _ history)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _ history)
    | archive_traffic_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
