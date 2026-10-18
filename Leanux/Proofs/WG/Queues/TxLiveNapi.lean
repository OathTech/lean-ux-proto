import Leanux.Proofs.WG.Queues.TxLivePoll

/-! The original saved NAPI scans and concrete Stack polls preserve the logical
TX live frontier on normal return. Their actual stopped prefixes remain appended;
no stopped endpoint is asserted. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveNapi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier

private theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Ready w.wg) a) :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product Ready
  unfold RxNapi.pendingSource
  exact preserves_bind
    (store_ready _ getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product Ready
  unfold RxNapi.scheduledSource
  exact preserves_bind
    (store_ready _ getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (LivePoll.stack pid budget)

theorem softirq_observed :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.product_transport) eq hi)
    pending_observed poll_observed

theorem inline_observed :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.product_transport) eq hi)
    pending_observed poll_observed

theorem irqExit_observed :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.product_transport) eq hi)
    scheduled_observed softirq_observed

theorem softirq :
    Preserves (fun w : World => Ready w.wg) Env.napiSoftirq :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.native_of_source) _ _ RxHistory.napiSoftirq_erases softirq_observed

theorem inline :
    Preserves (fun w : World => Ready w.wg) Env.pollScheduledInline :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.native_of_source) _ _ RxHistory.pollScheduledInline_erases inline_observed

theorem irqExit :
    Preserves (fun w : World => Ready w.wg) Env.napiIrqExit :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.native_of_source) _ _ RxHistory.napiIrqExit_erases irqExit_observed

end Leanux.Proofs.WG.Queues.TxDisposition.LiveNapi
