import Leanux.Proofs.WG.TransmitSecurity.BatchNativeTx

/-! Native send/clear work drains preserve queued batch alignment through
actual queue selection, handshake sends and final reference payment. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Deferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native

theorem flushed_send (pid : PeerId) : Preserves (Coherent locals active) (runFlushedSendWork pid) :=
  coherent_join (OccurrenceDeferred.flushed_send pid)
    (contents_wire (OccurrenceDeferred.flushed_send_contents pid) (OccurrenceDeferred.flushed_send_wire pid))

theorem queued_zero (pid : PeerId) : Preserves (Coherent locals active) (queuedExpiredZeroKeyMaterial pid) := by
  apply coherent_join (OccurrenceTimers.queued_zero pid)
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshake_clear pid) fun _ =>
    preserves_bind (clear pid) fun _ => Native.peer_put (some pid)

theorem flushed_clear (pid : PeerId) : Preserves (Coherent locals active) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact queued_zero _)
    | batch_coherent_step

theorem send_one : Preserves (fun w : World => Coherent locals active w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_send pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem clear_one : Preserves (fun w : World => Coherent locals active w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid)
    w.wg beforeWorker () v.wg v.ambient before worker

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Deferred
