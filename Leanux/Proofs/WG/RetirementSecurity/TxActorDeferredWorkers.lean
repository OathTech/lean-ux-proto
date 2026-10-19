import Leanux.Proofs.WG.RetirementSecurity.TxActorTimers

/-! Native queued send/clear dispatch retains actual TX service. Recorded
unit resolution is included; both source sections surround the original work
body, and the selected peer is not guessed from a queue projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
namespace TxSuspension

theorem flushed_send (pid : PeerId) : Keeps (runFlushedSendWork pid) := by
  suspension_source [runFlushedSendWork] using [modify_device,peer,device,set_peer,hidden,invariant,send_worker]

theorem flushed_clear (pid : PeerId) : Keeps (runFlushedClearWork pid) := by
  suspension_source [runFlushedClearWork] using [modify_device,hidden,clear_worker]

theorem send_one : SameView suspended Env.runOneSendWorker := by
  intro initial
  let P:=fun w=>suspended w=initial
  have read:Preserves P (liftWG getDev) := product device initial
  have peek (worker : Worker) : Preserves P (peekUnit worker : Leanux.M (Option Nat)) :=
    product_ambient (TxActorFrames.peek_unit worker) initial
  have resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
      Preserves P (resolveUnit worker unit queue : Leanux.M PeerId) :=
    product_ambient (TxActorFrames.resolve worker unit queue) initial
  have worker (pid : PeerId) : Preserves P (liftWG (runFlushedSendWork pid)) := product (flushed_send pid) initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  change Preserves P _
  rw [SendEnvironment.runOneSendWorker_factor]
  routing_tx_source [] using [read,peek,resolve,worker,stopped]

theorem clear_one : SameView suspended Env.runOneClearWorker := by
  intro initial
  let P:=fun w=>suspended w=initial
  have read:Preserves P (liftWG getDev) := product device initial
  have peek (worker : Worker) : Preserves P (peekUnit worker : Leanux.M (Option Nat)) :=
    product_ambient (TxActorFrames.peek_unit worker) initial
  have resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
      Preserves P (resolveUnit worker unit queue : Leanux.M PeerId) :=
    product_ambient (TxActorFrames.resolve worker unit queue) initial
  have worker (pid : PeerId) : Preserves P (liftWG (runFlushedClearWork pid)) := product (flushed_clear pid) initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  change Preserves P _
  rw [ClearWork.runOneClearWorker_factor]
  routing_tx_source [] using [read,peek,resolve,worker,stopped]
end TxSuspension
namespace TxWork

theorem serving_flushed_send (pid : PeerId) : Preserves (Serving locals crypt tx) (runFlushedSendWork pid) := by
  apply serving_join
  · apply passive_contents (OccurrenceDeferred.flushed_send_wire pid) (OccurrenceDeferred.flushed_send_contents pid)
    intro initial
    change Preserves (fun w=>queued w=initial) _
    unfold runFlushedSendWork
    simp (config := {zeta := false}) only [hidden,invariant]
    repeat' first
      | (rx_retention_head handshakeSendWorker; exact (send_worker_work _).wp (·=initial))
      | handshake_work_step initial
  · exact TxCovered.join (OccurrenceDeferred.flushed_send pid) (TxCoverageDeferred.flushed_send pid)

theorem serving_flushed_clear (pid : PeerId) : Preserves (Serving locals crypt tx) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact serving_queued_zero _)
    | serving_metadata_step

theorem serving_send_one : Preserves (fun w:World=>Serving locals crypt tx w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩:=SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (serving_flushed_send pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem serving_clear_one : Preserves (fun w:World=>Serving locals crypt tx w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩:=ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (serving_flushed_clear pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem send_one_actor : Preserves (At (Covered locals crypt) crypt active) Env.runOneSendWorker :=
  At.product (fun _=>serving_send_one) TxSuspension.send_one

theorem clear_one_actor : Preserves (At (Covered locals crypt) crypt active) Env.runOneClearWorker :=
  At.product (fun _=>serving_clear_one) TxSuspension.clear_one

end TxWork
end Leanux.Proofs.WG.RetirementSecurity
