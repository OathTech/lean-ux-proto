import Leanux.Proofs.WG.Queues.HolderCryptWorkers
import Leanux.Proofs.WG.Queues.HolderSendDispatch
import Leanux.Proofs.WG.Queues.RxDrainBoundary

/-! Actual deferred send dispatch pays one selected ordered occurrence, then
runs the original scheduler with the same committed RX-removal cut. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HolderScheduler RxRing

/-- The existing saved-state initiation observation includes the whole
physical RX ring; the terminal nullable peer payment retains it too. -/
theorem sendWorker_cell (pid : PeerId) : SameView RxRing.nativeCell (handshakeSendWorker pid) := by
  have send : SameView RxRing.nativeCell (sendHandshakeInitiation pid) :=
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendHandshakeInitiation_view) pid).of_factor
      (fun s => s.map fun d =>
        ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.epoch) d,
         (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.ring) d)) RxRing.nativeCell (fun w => by
        change w.dev.map (fun d => (d.ifindex,d.decryptQueue)) = (w.dev.map _).map _
        rw [Option.map_map]
        rfl)
  unfold handshakeSendWorker
  exact send.bind (fun _ => RxRing.peerPut_frame (some pid))

theorem flushedSend_cell (pid : PeerId) : SameView RxRing.nativeCell (runFlushedSendWork pid) := by
  ring_cell_source [runFlushedSendWork] using [sendWorker_cell]

theorem sendOne_cell : SameView RxRing.cell Env.runOneSendWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushedSend_cell pid)
    w.wg beforeWorker () v.wg v.ambient worker

theorem sendOne_boundary : Preserves (fun w : World => Boundary cs loans w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨pid,o,rest,_,post,stable⟩ := runOneSendWorker_funded w v funded stable run
  exact ⟨holders.withoutSend rest,post,stable⟩

/-- A real poll-free audit can change holders, including paying a selected
work occurrence. Its original audit suffix contributes no RX-removal event. -/
theorem audit_preserves (action : AuditM α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) original)
    (ring : SameView RxRing.cell original) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) (RxHistory.audit action) := by
  apply PrefixEnsures.preserves
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  obtain ⟨old,history,funded⟩ := hi.1
  have actual := (RxHistory.audit_erases erase w h).symm.trans run
  refine ⟨?_,?_⟩
  · apply HolderDecryptHistory.quiet_cut (Appends.focus _ _ _) _ history (Prod.ext run rfl)
      ((hoare_iff_run _ _ _).mp (keeps _) w x v funded actual)
    intro w h
    exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
      (fun _ => rfl) action w h
  · obtain ⟨epoch,n,j,r,refines,cell⟩ := hi.2
    exact ⟨epoch,n,j,r,refines,
      ((ProjectedAction.iff_run _ _ _).mp ring w x v actual).trans cell⟩

theorem sendOne_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      (RxHistory.audit runOneSendWorkerAudit) :=
  audit_preserves _ _ runOneSendWorkerAudit_erases (fun _ => sendOne_boundary) sendOne_cell

private theorem drained_store (what : String) (queues : List Bool) :
    SameProductStore (Env.requireDrained what queues) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases x
  exact congrArg productStoreView (requireDrained_normal what queues w v run).1

theorem drained_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (what : String) (queues : List Bool) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      (RxHistory.mixed (requireDrainedPrefix what queues)) := by
  change PrefixPreserves _ _ (RxHistory.audit (auditFocus (requireDrainedPrefix what queues)))
  exact audit_preserves _ _ (auditFocus_erases (requireDrainedPrefix_erases what queues))
    (fun _ => HolderEncrypt.product_store_boundary (drained_store what queues))
    ((drained_store what queues).of_factor
      (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue)) RxRing.cell (fun _ => rfl))

/-- The original record budget, saved queue selection and schedule after each
paid send item are unchanged. Duplicates are separate funded occurrences. -/
theorem runSendWorkers_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) RxHistory.runSendWorkers := by
  have safe : ∀ h w, HolderScheduler.Inv initial loans before h w → True := fun _ _ _ => True.intro
  have saved : ∀ h w v, productStoreView v = productStoreView w →
      HolderScheduler.Inv initial loans before h w → HolderScheduler.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderScheduler.store hi same
  unfold RxHistory.runSendWorkers
  repeat' first
    | (scheduler_preserve_at runOneSendWorkerAudit; exact sendOne_preserves initial loans before)
    | (scheduler_preserve_at RxHistory.schedule; exact HolderScheduler.schedule_preserves initial loans before receive _)
    | deferred_raw_steps safe saved

theorem afterXmit_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) RxHistory.afterXmit := by
  have safe : ∀ h w, HolderScheduler.Inv initial loans before h w → True := fun _ _ _ => True.intro
  have saved : ∀ h w v, productStoreView v = productStoreView w →
      HolderScheduler.Inv initial loans before h w → HolderScheduler.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderScheduler.store hi same
  unfold RxHistory.afterXmit
  repeat' first
    | (scheduler_preserve_at RxHistory.runCryptWorkers; exact runCryptWorkers_preserves initial loans before receive)
    | (scheduler_preserve_at RxHistory.runSendWorkers; exact runSendWorkers_preserves initial loans before receive)
    | (scheduler_preserve_at requireDrainedPrefix; exact drained_preserves initial loans before _ _)
    | deferred_raw_steps safe saved

/-- Native send draining uses the same original observed journal, rather than
assuming that scheduling cannot consume RX packets. -/
theorem runSendWorkers_normal (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : Env.runSendWorkers.run w = .ok ((),v)) :
    (∃ suffix, (runPrefix RxHistory.runSendWorkers w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v := by
  have actual := (RxHistory.runSendWorkers_erases w h).trans run
  have post := (runSendWorkers_preserves cs loans h receive w h
    ⟨HolderNapi.at_start funded h,physical⟩).choose_spec.2.2
  simpa only [actual,HolderScheduler.Inv,HolderNapi.At] using post

theorem afterXmit_normal (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : Env.afterXmit.run w = .ok ((),v)) :
    (∃ suffix, (runPrefix RxHistory.afterXmit w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v := by
  have actual := (RxHistory.afterXmit_erases w h).trans run
  have post := (afterXmit_preserves cs loans h receive w h
    ⟨HolderNapi.at_start funded h,physical⟩).choose_spec.2.2
  simpa only [actual,HolderScheduler.Inv,HolderNapi.At] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderDeferred
