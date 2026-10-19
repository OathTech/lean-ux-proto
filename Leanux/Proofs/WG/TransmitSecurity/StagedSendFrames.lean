import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeAdapters
import Leanux.Proofs.WG.RetirementSecurity.ClearedSlotFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferredWorkers

/-! Native send-worker preparation retains the saved peer's staged queue;
reference release may delete that peer after sending. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

theorem Exact.send_preparation (pid : PeerId) : SameView stagedAt (ClearedSlots.sendPreparation pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold ClearedSlots.sendPreparation
  apply preserves_bind ((Exact.modify_device (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp (· = initial))
  intro _
  apply hoare_bind _ _ (Staged.read_saved (fun queues => queues = initial) pid)
  intro peer
  let P := fun queues : PeerId → Option (Nat × List Packet) =>
    queues = initial ∧ queues pid = some (peer.internalId,peer.staged)
  have tail : Hoare (do
      let device ← getDev
      setPeer pid {peer with handshakePending := device.sendWorkQueue.contains pid}
      _ ← hidden (.sectionStart .sendWorker))
      (fun w => P (stagedAt w)) (fun _ w => stagedAt w = initial) := by
    apply hoare_bind _ _ ((Exact.store getDev_sameWGStore).wp P)
    intro device
    apply hoare_bind _ _ (Staged.write_saved (fun queues => queues = initial) pid
      {peer with handshakePending := device.sendWorkQueue.contains pid})
    intro _
    exact preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker))
      (fun w => stagedAt w = initial)) (fun _ => preserves_pure ())
  split
  · exact hoare_bind _ _ (hoare_liftAmbient (AmbientM.invariant "queued work without a pending flag")
      (fun w => P (stagedAt w))) (fun _ => tail)
  · exact tail

theorem send_initiation (pid : PeerId) : Frame (sendHandshakeInitiation pid) := by
  intro initial
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Retains initial))
    | (rx_retention_head createInitiation; exact create_initiation _ initial)
    | (rx_retention_head addMacToPacket; exact add_mac _ _ initial)
    | (rx_retention_head timersTraversal; exact of_view _ (Exact.traversal _) initial)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact of_view _ (Exact.delete_timer _ _) initial)
    | (rx_retention_head sendBufferToPeer; exact of_view _ (Exact.send_buffer _ _) initial)
    | (rx_retention_head timersHandshakeInitiated
       unfold timersHandshakeInitiated
       repeat' first
         | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Retains initial))
         | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (Retains initial))
         | (rx_retention_head modPeerTimerGuard; exact of_view _ (Exact.timer_guard _) initial)
         | (rx_retention_head armTimer; exact of_view _ (Exact.arm _ _ _ _) initial)
         | staged_handshake_step initial)
    | staged_handshake_step initial

theorem send_worker (pid : PeerId) : Frame (handshakeSendWorker pid) := by
  intro initial
  exact preserves_bind (send_initiation pid initial) (fun _ => peer_put (some pid) initial)

theorem flushed_send (pid : PeerId) : Frame (runFlushedSendWork pid) := by
  intro initial
  rw [ClearedSlots.send_factor]
  exact preserves_bind (of_view _ (Exact.send_preparation pid) initial) (fun _ =>
    preserves_bind (send_worker pid initial) (fun _ =>
      preserves_bind (hoare_liftAmbient _ (Retains initial)) (fun _ => preserves_pure _)))

theorem Origins.Native.flushed_send (pid : PeerId) : Preserves (Origins.Inv h) (runFlushedSendWork pid) :=
  Origins.frame (PacketOrigins.epoch_ring ((OccurrenceDeferred.flushed_send_wire pid).factor Prod.fst))
    (Staged.flushed_send pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged
