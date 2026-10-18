import Leanux.Proofs.WG.Roaming.RemoteDriverPollSource
import Leanux.Proofs.WG.Roaming.RemoteDriverCaptureSource
import Leanux.Proofs.WG.Queues.RxWaitAppends
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.DeferredPreservation
import Leanux.Proofs.WG.Index.TimerProductRulesSource
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.EnvClearDispatch

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Deferred
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem send_retained (entry : RemoteMap) :
    Preserves (fun w : World=>RemoteSilent.Retained entry w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    RxCredits.SendEnvironment.runOneSendWorker_selected w v run
  exact RemoteMaintenance.flushedSend entry pid w.wg beforeWorker () v.wg v.ambient pre worker

theorem clear_retained (entry : RemoteMap) :
    Preserves (fun w : World=>RemoteSilent.Retained entry w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    RxCredits.ClearWork.runOneClearWorker_selected w v run
  exact RemoteSilent.flushedClear entry pid w.wg beforeWorker () v.wg v.ambient pre worker

theorem section_retained (entry : RemoteMap) (worker : Worker) (body : Leanux.M Unit)
    (normal : Preserves (fun w : World=>RemoteSilent.Retained entry w.wg) body) :
    Preserves (fun w : World=>RemoteSilent.Retained entry w.wg) (Env.runTimerSection worker body) :=
  TimerDiscipline.runTimerSection_kernel_contract worker body
    (fun wg _ _ _=>RemoteSilent.Retained entry wg)
    (fun wg _ _ _=>RemoteSilent.Retained entry wg) normal

theorem timer_retained (entry : RemoteMap) (worker : Worker) (pid : PeerId)
    (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    Preserves (fun w : World=>RemoteSilent.Retained entry w.wg)
      (timerDispatchUnit worker pid timer wheel prior) :=
  Index.TimerProductRules.dispatch _ (fun {_}=>RemoteWorkers.product_store entry) (section_retained entry)
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (RemoteSilent.callback entry p t)))
    (fun p t=>PublicationPoll.native_product _ _ ((delTimer_remotes p t).wp (RemoteRetained entry)))
    worker pid timer wheel prior

theorem placeholder_retained (entry : RemoteMap) (j : UInt64) :
    Preserves (fun w : World=>RemoteSilent.Retained entry w.wg)
      (RxHistory.placeholderTimerPassSource j) :=
  Index.TimerProductRules.placeholder _ (fun {_}=>RemoteWorkers.product_store entry) (section_retained entry)
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (RemoteSilent.callback entry p t)))
    (fun p t=>PublicationPoll.native_product _ _ ((delTimer_remotes p t).wp (RemoteRetained entry))) j

theorem atoms (entry : RemoteMap) :
    RxHistory.DeferredSource.AtomContracts (Inv entry) Safe (fun {_} a=>focus a) := by
  have auditStore {α : Type} (g : AuditM α) (a : Leanux.M α)
      (erases : ErasesPrefix g a) (frame : SameProductStore a) :
      PrefixPreserves (Inv entry) Safe (focus (RxHistory.audit g)) :=
    focus_store entry _ a (Appends.focus _ _ _) (RxHistory.audit_erases erases) frame
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact focus_retained entry _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases runOneSendWorkerAudit_erases) send_retained
  · exact focus_retained entry _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases runOneClearWorkerAudit_erases) clear_retained
  · intro what queues
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
      (PendingScheduler.requireDrained_store what queues)
  · exact auditStore _ _ getDevSavedAudit_erases (liftWG_sameProductStore _ getDev_sameWGStore)
  · intro d j; exact auditStore _ _ (wheelNextDueAudit_erases d j) (SameView.pure _ _)
  · intro b; exact auditStore _ _ (requireStepCompleteAudit_erases b) (PendingScheduler.requireStepComplete_store b)
  · intro j; exact auditStore _ _ (requireNothingDueAudit_erases j) (PendingScheduler.requireNothingDue_store j)
  · intro worker pid timer wheel prior
    exact focus_retained entry _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases (timerDispatchAudit_erases worker pid timer wheel prior))
      (fun before=>timer_retained before worker pid timer wheel prior)
  · intro j
    exact focus_retained entry _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j)) (fun before=>placeholder_retained before j)
  · exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases requireIdleDevicePrefix_erases) PendingScheduler.requireIdleDevice_store
  · exact auditStore _ _ (erasesPrefix_lift _) requireNoCryptWork_sameKernel
  · intro timer; exact auditStore _ _ (erasesPrefix_lift _) (timerWorker_sameKernel timer)
  · intro ticks; exact auditStore _ _ (advanceAudit_erases ticks) (advance_sameKernel ticks)
end Leanux.Proofs.WG.Roaming.RemoteDriver.Deferred
