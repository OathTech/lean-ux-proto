import Leanux.Proofs.WG.RetirementSecurity.TxCoverageScheduler
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferredWorkers

/-! Native send/clear work drains preserve resident TX coverage through
actual queue selection, handshake sends and final reference payment. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits TxCoverageNative

theorem flushed_send (pid : PeerId) : Preserves (TxCoverage locals) (runFlushedSendWork pid) :=
  contents_wire (OccurrenceDeferred.flushed_send_contents pid) (OccurrenceDeferred.flushed_send_wire pid)

theorem queued_zero (pid : PeerId) : Preserves (TxCoverage locals) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshake_clear pid) fun _ =>
    preserves_bind (clear pid) fun _ => TxCoverageNative.peer_put (some pid)

theorem flushed_clear (pid : PeerId) : Preserves (TxCoverage locals) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact queued_zero _)
    | coverage_native_step

theorem send_one : Preserves (fun w : World => TxCoverage locals w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_send pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem clear_one : Preserves (fun w : World => TxCoverage locals w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid)
    w.wg beforeWorker () v.wg v.ambient before worker

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeferred
