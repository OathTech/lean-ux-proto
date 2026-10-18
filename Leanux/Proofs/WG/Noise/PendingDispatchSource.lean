import Leanux.Proofs.WG.Noise.PendingMaintenanceSource
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.EnvClearDispatch

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

/-- Actual named/head selection leaves the entry WG state for the same
native flush. This includes the queue erase, pending guard and section records. -/
theorem run_one_send (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    RxCredits.SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_send pid seen)
    w.wg beforeWorker () v.wg v.ambient hi worker

theorem run_one_clear (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    RxCredits.ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid seen)
    w.wg beforeWorker () v.wg v.ambient hi worker

theorem run_one_send_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.audit runOneSendWorkerAudit) :=
  audit_observed _ _ runOneSendWorkerAudit_erases run_one_send

theorem run_one_clear_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.audit runOneClearWorkerAudit) :=
  audit_observed _ _ runOneClearWorkerAudit_erases run_one_clear

end Leanux.Proofs.WG.Noise.PendingSession
