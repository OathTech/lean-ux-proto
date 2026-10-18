import Leanux.Proofs.WG.Index.ReachedIndexSource
import Leanux.Proofs.WG.Index.HashSlotClearWorkerClaims
import Leanux.Proofs.WG.Index.RetirementClearWorkerClaims
import Leanux.Proofs.WG.Index.ClearSource
import Leanux.Proofs.WG.Index.InitiationIndexSource
import Leanux.Proofs.WG.Index.DispatchSource
import Leanux.Proofs.WG.Index.TimerCoreSource
import Leanux.Proofs.WG.Queues.HolderAuxTimers
import Leanux.Proofs.WG.Queues.BaseCoherenceDeferred

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedWorkers
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem clear_core :
    Noise.Product.Ensures Env.runOneClearWorker
      (fun w => Reached.Core w.wg) (fun _ w => Reached.Core w.wg) := by
  intro w result v pre run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  have index := runFlushedClearWork_hashSlots_coherent pid
    w.wg beforeWorker () v.wg v.ambient
    ⟨fun d hd => (pre d hd).2.1, fun d hd => (pre d hd).2.2.1⟩ worker
  have reserved := runFlushedClearWork_retirement [] pid
    w.wg beforeWorker () v.wg v.ambient
    (fun d hd => (pre d hd).2.2.2) worker
  have tables := runOneClearWorker_tables w () v
    (fun d hd => (pre d hd).1) run
  exact fun d hd => ⟨tables d hd,index.1 d hd,index.2 d hd,reserved d hd⟩

theorem clear_observed (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit runOneClearWorkerAudit) := by
  apply Reached.aux_pair _ initial loans before
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.clearOne)
  intro w h entry result v run
  have native := (RxHistory.audit_erases runOneClearWorkerAudit_erases w h).symm.trans run
  have base := BaseCoherence.transport entry.2.1
    ((ProjectedAction.iff_run _ _ _).mp
      (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.clearOne_view)
      w result v native)
  exact ⟨base,clear_core w result v entry.2.2 native⟩

theorem clear_normal {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w v : World}
    (entry : Reached.Aux initial loans before history w)
    (run : Env.runOneClearWorker.run w=.ok ((),v)) :
    let after := (runPrefix (RxHistory.audit runOneClearWorkerAudit) w history).2
    Reached.Aux initial loans before after v ∧
      ∃ suffix, after=before++suffix ∧
        Reached.Entry (remaining initial (NapiCarrier.removedPackets suffix)) loans after v := by
  have actual := (RxHistory.audit_erases runOneClearWorkerAudit_erases w history).trans run
  have post := (clear_observed initial loans before w history entry).choose_spec.2.2
  have reached : Reached.Aux initial loans before
      (runPrefix (RxHistory.audit runOneClearWorkerAudit) w history).2 v := by
    simpa only [actual] using post
  exact ⟨reached,Reached.aux_to_entry reached⟩

theorem send_boundary_core (cs : Ledger) (loans : Reservations) :
    Noise.Product.Ensures Env.runOneSendWorker
      (fun w => DeviceBoundary.Entry cs loans w.wg ∧ Reached.Core w.wg)
      (fun _ w => DeviceBoundary.Entry cs loans w.wg ∧ Reached.Core w.wg) := by
  intro w result v pre run
  cases result
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,device,_,_,_,member,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  obtain ⟨paid,rest,selected⟩ := WorkReservations.select_exists holders.send pid
    ((funded.aligned.send d device) ▸ member)
  have post := flushed_send_retirement holders cs pid paid rest [] loans selected
    (initiationIndexContract_actual (holders.withoutSend rest) cs paid [] loans)
    w.wg v.wg beforeWorker v.ambient pre.1.2.2 pre.1.2.1 funded stable
    ⟨fun d hd => (pre.2 d hd).2.1,fun d hd => (pre.2 d hd).2.2.1,
      fun d hd => (pre.2 d hd).2.2.2⟩ worker
  have tables := runOneSendWorker_tables w () v
    (fun d hd => (pre.2 d hd).1) run
  exact ⟨⟨⟨holders.withoutSend rest,post.1,post.2.1⟩,post.2.2.2.1,post.2.2.1⟩,
    fun d hd => ⟨tables d hd,post.2.2.2.2.1 d hd,post.2.2.2.2.2.1 d hd,
      post.2.2.2.2.2.2 d hd⟩⟩

theorem send_observed (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit runOneSendWorkerAudit) := by
  apply Reached.aux_pair _ initial loans before (HolderAuxSend.sendOne initial loans before)
  intro w h entry result v run
  have native := (RxHistory.audit_erases runOneSendWorkerAudit_erases w h).symm.trans run
  obtain ⟨suffix,_,fixed⟩ := Reached.aux_to_entry entry
  have post := send_boundary_core (remaining initial (NapiCarrier.removedPackets suffix)) loans
    w result v ⟨fixed.1.1.1,fixed.2⟩ native
  exact ⟨post.1.2.1,post.2⟩

theorem send_normal {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w v : World}
    (entry : Reached.Aux initial loans before history w)
    (run : Env.runOneSendWorker.run w=.ok ((),v)) :
    let after := (runPrefix (RxHistory.audit runOneSendWorkerAudit) w history).2
    Reached.Aux initial loans before after v ∧
      ∃ suffix, after=before++suffix ∧
        Reached.Entry (remaining initial (NapiCarrier.removedPackets suffix)) loans after v := by
  have actual := (RxHistory.audit_erases runOneSendWorkerAudit_erases w history).trans run
  have post := (send_observed initial loans before w history entry).choose_spec.2.2
  have reached : Reached.Aux initial loans before
      (runPrefix (RxHistory.audit runOneSendWorkerAudit) w history).2 v := by
    simpa only [actual] using post
  exact ⟨reached,Reached.aux_to_entry reached⟩

theorem callback_observed (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) (timer : PeerTimer) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) := by
  have erase := RxHistory.mixed_erases (liftWGObserver_erases (timerCallbackPrefix_erases pid timer))
  have account : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) := by
    apply HolderAuxiliary.pair
    · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.mixed)
        _ _ (liftWGObserver_erases (timerCallbackPrefix_erases pid timer))
        (fun _ => HolderTimers.callback_product pid timer)
      exact sameView_liftWG RxRing.cell RxRing.nativeCell _ (HolderTimerPhysical.callback_cell pid timer)
        (fun _ _ _ same => same)
    · exact OwnerTimers.timerCallback_checked pid timer
    · intro w h hi result v run
      have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
        (timerCallback pid timer) w v result ((erase w h).symm.trans run)
      exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Timer.callback pid timer)
        w.wg w.ambient result v.wg v.ambient hi.2.2 native
  apply Reached.aux_pair _ initial loans before account
  intro w h entry result v run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    (timerCallback pid timer) w v result ((erase w h).symm.trans run)
  have base := BaseCoherence.transport entry.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.timerCallback_view pid timer)
      w.wg w.ambient result v.wg v.ambient native)
  exact ⟨base,(TimerCore.callback pid timer w.wg w.ambient result v.wg v.ambient
    ⟨entry.1.2.2,entry.2.2⟩ native).2⟩

theorem callback_normal {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w v : World}
    (pid : PeerId) (timer : PeerTimer)
    (entry : Reached.Aux initial loans before history w)
    (run : (liftWG (timerCallback pid timer)).run w=.ok ((),v)) :
    let after := (runPrefix (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) w history).2
    Reached.Aux initial loans before after v ∧
      ∃ suffix, after=before++suffix ∧
        Reached.Entry (remaining initial (NapiCarrier.removedPackets suffix)) loans after v := by
  have actual := (RxHistory.mixed_erases (liftWGObserver_erases
    (timerCallbackPrefix_erases pid timer)) w history).trans run
  have post := (callback_observed initial loans before pid timer w history entry).choose_spec.2.2
  have reached : Reached.Aux initial loans before
      (runPrefix (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) w history).2 v := by
    simpa only [actual] using post
  exact ⟨reached,Reached.aux_to_entry reached⟩

end Leanux.Proofs.WG.Index.ReachedWorkers
