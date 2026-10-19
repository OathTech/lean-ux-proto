import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceConfigFrames

/-! Removing peers may run queued handshake work. Every native callback keeps
the archive, which retains the allocation after the peer disappears. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem drain_work (upTo : Option PeerId) :
    Framing.Preserves Inv (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushed_send _)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _)
    | peer_reference_traffic_step

theorem stop_timers (pid : PeerId) :
    Framing.Preserves Inv (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact del_timer _ _)
    | (rx_retention_head drainHandshakeSendWq; exact drain_work _)
    | peer_reference_traffic_step

theorem make_dead (pid : PeerId) :
    Framing.Preserves Inv (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact remove_ips _)
    | peer_reference_traffic_step

theorem after_dead (pid : PeerId) :
    Framing.Preserves Inv (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact clear_keys _)
    | (rx_retention_head timersStop; exact stop_timers _)
    | (rx_retention_head drainHandshakeSendWq; exact drain_work _)
    | peer_reference_traffic_step

theorem remove (peer : Option PeerId) :
    Framing.Preserves Inv (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | peer_reference_traffic_step

theorem remove_all :
    Framing.Preserves Inv peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_ips)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | peer_reference_traffic_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
