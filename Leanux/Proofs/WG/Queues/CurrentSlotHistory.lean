import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.Queues.NapiSource

/-! The existing NAPI and crypt observers retain the three-slot invariant on
their exact native/product executions. Incoming histories remain arbitrary,
and actual stopped prefixes are retained by the source append contracts. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem product_transport (same : productStoreView v = productStoreView w)
    (hi : Inv w.wg) : Inv v.wg := by
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  apply fields_transport hi
  unfold fields RxCredits.keyWords
  rw [dev]

/-- State-only transport uses the same actual normal run. On Stop, the exact
append contract retains the journal without manufacturing an endpoint. -/
theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Inv w.wg) a) :
    PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
    (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product Inv
  unfold RxNapi.pendingSource
  repeat' slot_traffic_step

private theorem scheduled_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
    (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product Inv
  unfold RxNapi.scheduledSource
  repeat' slot_traffic_step

theorem poll_observed (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) (RxHistory.observePoll pid budget) :=
  observed _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (poll_stack pid budget)

theorem softirq_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    pending_observed poll_observed

theorem inline_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    pending_observed poll_observed

theorem irqExit_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    scheduled_observed softirq_observed

theorem prepare_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
    Origins.HistoryAdapters.prepare :=
  observed _ _ (Appends.focus _ _ _) Origins.HistoryAdapters.prepare_erases
    (PublicationPoll.native_product Inv _ prepareSource_preserves)

theorem decryptStep_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) RxHistory.decryptStep := by
  apply NapiSource.decrypt_preserves (fun _ _ _ => True.intro) prepare_observed
    (fun pid => observed _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases (some pid))))
      (PublicationPoll.native_product Inv _ (peerPut_preserves (some pid))))
    softirq_observed irqExit_observed

theorem decryptIteration_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
    RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ _ => True.intro) decryptStep_observed
  apply PrefixPreserves.bind
    (observed _ _ (Appends.lift _) (erasesPrefix_lift _)
      (product_store_preserves (condResched_sameKernel .decryptWorker)))
  intro resched
  exact observed _ _ (Appends.lift _) (erasesPrefix_lift _)
    (productAmbient_spec (AmbientM.branch .decWorkerNeedResched resched) _ (fun _ _ hi => hi))

theorem encryptIteration_observed : PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
    RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  apply PrefixPreserves.bind
    (observed _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
      (PublicationPoll.native_product Inv _ encryptPoll_preserves))
  intro item
  apply PrefixPreserves.bind softirq_observed
  intro _
  exact observed _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases (RxWorkers.encryptTail_erases item))
    (encryptTail_preserves item)

end Leanux.Proofs.WG.CurrentSlots
