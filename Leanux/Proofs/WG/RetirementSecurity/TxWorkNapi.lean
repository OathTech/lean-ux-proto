import Leanux.Proofs.WG.RetirementSecurity.TxWorkStack

/-! Existing native NAPI factors retain the joint TX coverage/service carrier
for a fixed external actor list. Actual suspension frames are separate; these
facts do not assume arbitrary Ambient operations retain suspended records. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWorkNapi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxWork

private theorem product_transport (locals : List TxLocalBatch)
    (same : productStoreView v = productStoreView w)
    (hi : Serving locals crypt tx w.wg) : Serving locals crypt tx v.wg := by
  exact serving_store_transport (congrArg (fun s : ProductStore43 => s.2.2.2) same) hi

private theorem observed {E α : Type} (locals : List TxLocalBatch)
    (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Serving locals crypt tx w.wg) a) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed (locals : List TxLocalBatch) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed locals _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product (Serving locals crypt tx)
  unfold RxNapi.pendingSource
  exact preserves_bind
    (serving_store getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed (locals : List TxLocalBatch) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed locals _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product (Serving locals crypt tx)
  unfold RxNapi.scheduledSource
  exact preserves_bind
    (serving_store getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (locals : List TxLocalBatch) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed locals _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (serving_poll pid budget _ stackForM_stack)

theorem softirq_observed (locals : List TxLocalBatch) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals eq hi)
    (pending_observed locals) (poll_observed locals)

theorem inline_observed (locals : List TxLocalBatch) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals eq hi)
    (pending_observed locals) (poll_observed locals)

theorem irqExit_observed (locals : List TxLocalBatch) :
    PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals eq hi)
    (scheduled_observed locals) (softirq_observed locals)

private theorem native {α : Type} (locals : List TxLocalBatch)
    (g : RxHistory.Obs α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ w => Serving locals crypt tx w.wg) (fun _ => True) g) :
    Preserves (fun w : World => Serving locals crypt tx w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have actual := (erases w []).trans run
  have post := (keep w [] hi).choose_spec.2.2
  rw [actual] at post
  exact post

theorem softirq (locals : List TxLocalBatch) :
    Preserves (fun w : World => Serving locals crypt tx w.wg) Env.napiSoftirq :=
  native locals _ _ RxHistory.napiSoftirq_erases (softirq_observed locals)

theorem inline (locals : List TxLocalBatch) :
    Preserves (fun w : World => Serving locals crypt tx w.wg) Env.pollScheduledInline :=
  native locals _ _ RxHistory.pollScheduledInline_erases (inline_observed locals)

theorem irqExit (locals : List TxLocalBatch) :
    Preserves (fun w : World => Serving locals crypt tx w.wg) Env.napiIrqExit :=
  native locals _ _ RxHistory.napiIrqExit_erases (irqExit_observed locals)

end Leanux.Proofs.WG.RetirementSecurity.TxWorkNapi
