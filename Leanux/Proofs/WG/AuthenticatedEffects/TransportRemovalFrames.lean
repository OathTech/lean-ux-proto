import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierDeferredFrames
import Leanux.Proofs.WG.Packets.PublicationRemoval

/-! Native removal can flush handshake work and retire keys. Those real paths
preserve the RX cell projection, including its device epoch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportRemoval
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
open OwnerCompletion (geometry)
set_option maxHeartbeats 600000

theorem sendWorker_geometry (pid : PeerId) : SameView geometry (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact SameView.bind (PublicationGeometry.sendHandshakeInitiation_geometry pid)
    (fun _ => (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.peerPay) (some pid))

theorem flushedSend_geometry (pid : PeerId) : SameView geometry (runFlushedSendWork pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [invariant,hidden]
  repeat' first
    | (allocation_release_head handshakeSendWorker; exact (sendWorker_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem flushedClear_geometry (pid : PeerId) : SameView geometry (runFlushedClearWork pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold runFlushedClearWork queuedExpiredZeroKeyMaterial
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (allocation_release_head handshakeClear
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.handshakeClear_geometry) _).wp (fun s => s = initial))
    | (allocation_release_head keypairsClear
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.keypairsClear_geometry) _).wp (fun s => s = initial))
    | completion_step initial

theorem drain_geometry (upTo : Option PeerId) : SameView geometry (drainHandshakeSendWq upTo) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (allocation_release_head runFlushedSendWork; exact (flushedSend_geometry _).wp (fun s => s = initial))
    | (allocation_release_head runFlushedClearWork; exact (flushedClear_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem timersStop_geometry (pid : PeerId) : SameView geometry (timersStop pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersStop
  repeat' first
    | (allocation_release_head delTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) _ _).wp (fun s => s = initial))
    | (allocation_release_head drainHandshakeSendWq; exact (drain_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem removeAfter_geometry (pid : PeerId) : SameView geometry (peerRemoveAfterDead pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head keypairsClear
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.keypairsClear_geometry) _).wp (fun s => s = initial))
    | (allocation_release_head timersStop; exact (timersStop_geometry _).wp (fun s => s = initial))
    | (allocation_release_head drainHandshakeSendWq; exact (drain_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem dead_geometry (pid : PeerId) : SameView geometry (peerMakeDead pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head removeByPeer; exact (PublicationFrontier.removeByPeer_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem remove_geometry (peer : Option PeerId) : SameView geometry (peerRemove peer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head peerMakeDead; exact (dead_geometry _).wp (fun s => s = initial))
    | (allocation_release_head peerRemoveAfterDead; exact (removeAfter_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem removeAll_geometry : SameView geometry peerRemoveAll := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head WG.free
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationRemoval.«0».Leanux.Proofs.WG.PublicationFrontier.allowedipsFree_geometry).wp (fun s => s = initial))
    | (allocation_release_head peerMakeDead; exact (dead_geometry _).wp (fun s => s = initial))
    | (allocation_release_head peerRemoveAfterDead; exact (removeAfter_geometry _).wp (fun s => s = initial))
    | completion_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TransportRemoval
