import Leanux.Proofs.WG.RetirementSecurity.KeySlotPoll
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceNapi

/-! Actual saved NAPI scans retain live published slots through the concrete
stack poll. Existing source observers supply the native control-flow factor. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open KeySlotLiveness

private theorem product_transport (pending : List PeerId)
    (same : productStoreView v = productStoreView w)
    (hi : InvExcept pending w.wg) : InvExcept pending v.wg := by
  exact store_transport (congrArg (fun s : ProductStore43 => s.2.2.2) same) hi

private theorem observed {E α : Type} (pending : List PeerId)
    (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => InvExcept pending w.wg) a) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed (pending : List PeerId) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed pending _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product (InvExcept pending)
  unfold RxNapi.pendingSource
  exact preserves_bind
    (KeySlotLiveness.store getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed (pending : List PeerId) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed pending _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product (InvExcept pending)
  unfold RxNapi.scheduledSource
  exact preserves_bind
    (KeySlotLiveness.store getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (pending : List PeerId) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed pending _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (KeySlotLiveness.stack pid budget)

theorem softirq_observed (pending : List PeerId) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport pending eq hi)
    (pending_observed pending) (poll_observed pending)

theorem inline_observed (pending : List PeerId) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport pending eq hi)
    (pending_observed pending) (poll_observed pending)

theorem irqExit_observed (pending : List PeerId) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport pending eq hi)
    (scheduled_observed pending) (softirq_observed pending)

private theorem native {α : Type} (pending : List PeerId)
    (g : RxHistory.Obs α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) g) :
    Preserves (fun w : World => InvExcept pending w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have actual := (erases w []).trans run
  have post := (keep w [] hi).choose_spec.2.2
  rw [actual] at post
  exact post

theorem softirq (pending : List PeerId) :
    Preserves (fun w : World => InvExcept pending w.wg) Env.napiSoftirq :=
  native pending _ _ RxHistory.napiSoftirq_erases (softirq_observed pending)

theorem inline (pending : List PeerId) :
    Preserves (fun w : World => InvExcept pending w.wg) Env.pollScheduledInline :=
  native pending _ _ RxHistory.pollScheduledInline_erases (inline_observed pending)

theorem irqExit (pending : List PeerId) :
    Preserves (fun w : World => InvExcept pending w.wg) Env.napiIrqExit :=
  native pending _ _ RxHistory.napiIrqExit_erases (irqExit_observed pending)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi
