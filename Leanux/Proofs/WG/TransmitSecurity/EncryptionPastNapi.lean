import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastRxPoll

/-! Actual NAPI scans and concrete Stack polls preserve the supplied historical
encryption exclusion and physical frontier. Appended Stop prefixes carry no
returned World. Initialization of this carrier remains a separate obligation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Napi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.TxDisposition
variable {past : List (Option Nat × SkbId)} {active : List (List SkbId)}

theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Ready past active w.wg) a) :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product (Ready past active)
  unfold RxNapi.pendingSource
  exact preserves_bind
    (ready_store getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product (Ready past active)
  unfold RxNapi.scheduledSource
  exact preserves_bind
    (ready_store getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (stack_poll pid budget)

theorem softirq_observed :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    pending_observed poll_observed

theorem inline_observed :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    pending_observed poll_observed

theorem irqExit_observed :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport eq hi)
    scheduled_observed softirq_observed

theorem softirq :
    Preserves (fun w : World => Ready past active w.wg) Env.napiSoftirq :=
  native_of_source _ _ RxHistory.napiSoftirq_erases softirq_observed

theorem inline :
    Preserves (fun w : World => Ready past active w.wg) Env.pollScheduledInline :=
  native_of_source _ _ RxHistory.pollScheduledInline_erases inline_observed

theorem irqExit :
    Preserves (fun w : World => Ready past active w.wg) Env.napiIrqExit :=
  native_of_source _ _ RxHistory.napiIrqExit_erases irqExit_observed

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Napi
