import Leanux.Proofs.WG.Index.PollCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem history_poll (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) (RxHistory.observePoll pid budget) :=
  observed _ _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (poll_ready pid budget)

theorem history_native {α : Type} (g : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix g action) (keep : Preserves TimerCore.Ready action) :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver g))) :=
  observed _ _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases erase)))
    (PublicationPoll.native_product _ _ keep)

theorem pending_scan :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix))) := by
  apply history_native _ _ RxNapi.pending_erases
  apply store_ready
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun _=>SameView.pure _ _)

theorem scheduled_scan :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))) := by
  apply history_native _ _ RxNapi.scheduled_erases
  apply store_ready
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun _=>SameView.pure _ _)

theorem softirq_observed :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same pre=>TransmitCore.ready_product_store same pre)
    pending_scan history_poll

theorem inline_observed :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same pre=>TransmitCore.ready_product_store same pre)
    pending_scan history_poll

theorem irqExit_observed :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same pre=>TransmitCore.ready_product_store same pre)
    scheduled_scan softirq_observed

theorem softirq_ready : Preserves (fun w : World=>TimerCore.Ready w.wg) Env.napiSoftirq :=
  original _ _ _ RxHistory.napiSoftirq_erases softirq_observed

theorem inline_ready : Preserves (fun w : World=>TimerCore.Ready w.wg) Env.pollScheduledInline :=
  original _ _ _ RxHistory.pollScheduledInline_erases inline_observed

theorem irqExit_ready : Preserves (fun w : World=>TimerCore.Ready w.wg) Env.napiIrqExit :=
  original _ _ _ RxHistory.napiIrqExit_erases irqExit_observed

end Leanux.Proofs.WG.Index.PollCore
