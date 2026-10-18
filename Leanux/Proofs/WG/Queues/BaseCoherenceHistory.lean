import Leanux.Proofs.WG.Queues.BaseCoherenceWorkers
import Leanux.Proofs.WG.Queues.NapiSource

/-! Exact structural frames on the original receive, NAPI and crypt journals.
Normal endpoints retain the view; failed executions retain their actual
appended journal, with no invented final World. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem product_view_transport (same : productStoreView v=productStoreView w) :
    view v.wg=view w.wg :=
  congrArg (fun s : ProductStore43 => view {dev:=s.2.2.2.dev}) same

theorem native_product_view {α : Type} (a : WG.M α) (frame : SameView view a) :
    SameView (fun w : World => view w.wg) (liftWG a) :=
  sameView_liftWG _ view a frame (fun _ _ _ same => same)

theorem observed_structure {E α : Type} (initial) (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : SameView (fun w : World => view w.wg) a) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ((ProjectedAction.iff_run _ _ _).mp keeps w out.1 out.2 ((erases w h).symm.trans run)).trans hi

private theorem pending_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
    (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed_structure initial _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply native_product_view
  intro s
  change Preserves (fun w => view w=s) _
  unfold RxNapi.pendingSource
  repeat' base_rx_step s

private theorem scheduled_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
    (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed_structure initial _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply native_product_view
  intro s
  change Preserves (fun w => view w=s) _
  unfold RxNapi.scheduledSource
  repeat' base_rx_step s

theorem poll_structure (initial) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.observePoll pid budget) :=
  observed_structure initial _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (poll_stack_view pid budget)

theorem softirq_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (product_view_transport eq).trans hi)
    (pending_structure initial) (poll_structure initial)

theorem inline_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (product_view_transport eq).trans hi)
    (pending_structure initial) (poll_structure initial)

theorem irqExit_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (product_view_transport eq).trans hi)
    (scheduled_structure initial) (softirq_structure initial)

theorem prepare_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
    Origins.HistoryAdapters.prepare :=
  observed_structure initial _ _ (Appends.focus _ _ _) Origins.HistoryAdapters.prepare_erases
    (native_product_view _ prepareSource_view)

theorem decryptStep_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.decryptStep := by
  apply NapiSource.decrypt_preserves (fun _ _ _ => True.intro) (prepare_structure initial)
    (fun pid => observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases (some pid))))
      (native_product_view _ (peerPut_view (some pid))))
    (softirq_structure initial) (irqExit_structure initial)

theorem decryptIteration_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
    RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ _ => True.intro) (decryptStep_structure initial)
  apply PrefixPreserves.bind
    (observed_structure initial _ _ (Appends.lift _) (erasesPrefix_lift _)
      (product_store_view (condResched_sameKernel .decryptWorker)))
  intro resched
  exact observed_structure initial _ _ (Appends.lift _) (erasesPrefix_lift _)
    (fun _ => productAmbient_spec (AmbientM.branch .decWorkerNeedResched resched) _ (fun _ _ hi => hi))

theorem encryptIteration_structure (initial) : PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
    RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  apply PrefixPreserves.bind
    (observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
      (native_product_view _ encryptPoll_view))
  intro item
  apply PrefixPreserves.bind (softirq_structure initial)
  intro _
  exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases (RxWorkers.encryptTail_erases item))
    (encryptTail_view item)

theorem txIteration_structure (initial) (pid : PeerId) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  observed_structure initial _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _)))
    (txIter_view pid _ (product_store_view (condResched_sameKernel .txWorker)))

theorem receiveIteration_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) Origins.HistoryAdapters.receiveIteration := by
  unfold Origins.HistoryAdapters.receiveIteration
  exact workerIterPrefix_preserves _ _ (fun _ _ _ => True.intro)
    (observed_structure initial _ _ (Appends.focus _ _ _) Origins.HistoryAdapters.receiveStep_erases
      (native_product_view _ receiveStep_view))
    (observed_structure initial _ _ (Appends.lift _) (erasesPrefix_lift _)
      (product_store_view (condResched_sameKernel .receiveWorker)))

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
