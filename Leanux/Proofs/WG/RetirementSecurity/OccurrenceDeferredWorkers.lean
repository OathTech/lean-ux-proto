import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers
import Leanux.Proofs.WG.Queues.SendEnvironment

/-! Actual queued handshake and clear dispatch retains physical TX owners.
Queue selection comes from the native recorded resolver or legacy head. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

theorem flushed_send_wire (pid : PeerId) : SameView txCryptWire (runFlushedSendWork pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [hidden,invariant]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact (send_worker_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem flushed_send_contents (pid : PeerId) : SameView txQueueContents (runFlushedSendWork pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [hidden,invariant]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact (send_worker_contents _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem zero_wire (pid : PeerId) : SameView txCryptWire (queuedExpiredZeroKeyMaterial pid) :=
  (OccurrenceKeys.handshake_clear_wire pid).bind (fun _ =>
    (OccurrenceKeys.clear_wire pid).bind (fun _ => peerPut_cryptWire (some pid)))

theorem flushed_clear_wire (pid : PeerId) : SameView txCryptWire (runFlushedClearWork pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact (zero_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem flushed_send (pid : PeerId) : Preserves (Ready locals active) (runFlushedSendWork pid) :=
  RxPollOccurrences.join (PeerRemovalCall.erases (.sendWork pid))
    (PeerRemovalCall.allocation (.sendWork pid))
    (occurrences_queueContents (flushed_send_wire pid) (flushed_send_contents pid))

theorem flushed_clear (pid : PeerId) : Preserves (Ready locals active) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact OccurrenceTimers.queued_zero _)
    | occurrence_ready_step

theorem send_one : Preserves (fun w : World => Ready locals active w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_send pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem clear_one : Preserves (fun w : World => Ready locals active w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem send_one_wire : SameView (fun w : World => txCryptWire w.wg) Env.runOneSendWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushed_send_wire pid)
    w.wg beforeWorker () v.wg v.ambient worker

theorem clear_one_wire : SameView (fun w : World => txCryptWire w.wg) Env.runOneClearWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushed_clear_wire pid)
    w.wg beforeWorker () v.wg v.ambient worker

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferred
