import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativePoll

/-! Actual NAPI scans preserve ready ciphertext coherence through every saved poll
selection and both callback placements. The existing source erasure is exact. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Napi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity Native Stack

private theorem product_transport (locals : List TxLocalBatch) (active : List (List SkbId))
    (same : productStoreView v = productStoreView w)
    (hi : Coherent locals active w.wg) : Coherent locals active v.wg := by
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) hi

private theorem observed {E α : Type} (locals : List TxLocalBatch) (active : List (List SkbId))
    (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Coherent locals active w.wg) a) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed (locals : List TxLocalBatch) (active : List (List SkbId)) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed locals active _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product (Coherent locals active)
  unfold RxNapi.pendingSource
  exact preserves_bind
    (Poll.store getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed (locals : List TxLocalBatch) (active : List (List SkbId)) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed locals active _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product (Coherent locals active)
  unfold RxNapi.scheduledSource
  exact preserves_bind
    (Poll.store getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (locals : List TxLocalBatch) (active : List (List SkbId)) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed locals active _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (Poll.stack pid budget)

theorem softirq_observed (locals : List TxLocalBatch) (active : List (List SkbId)) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals active eq hi)
    (pending_observed locals active) (poll_observed locals active)

theorem inline_observed (locals : List TxLocalBatch) (active : List (List SkbId)) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals active eq hi)
    (pending_observed locals active) (poll_observed locals active)

theorem irqExit_observed (locals : List TxLocalBatch) (active : List (List SkbId)) :
    PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport locals active eq hi)
    (scheduled_observed locals active) (softirq_observed locals active)

private theorem native {α : Type} (locals : List TxLocalBatch) (active : List (List SkbId))
    (g : RxHistory.Obs α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ w => Coherent locals active w.wg) (fun _ => True) g) :
    Preserves (fun w : World => Coherent locals active w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have actual := (erases w []).trans run
  have post := (keep w [] hi).choose_spec.2.2
  rw [actual] at post
  exact post

theorem softirq (locals : List TxLocalBatch) (active : List (List SkbId)) :
    Preserves (fun w : World => Coherent locals active w.wg) Env.napiSoftirq :=
  native locals active _ _ RxHistory.napiSoftirq_erases (softirq_observed locals active)

theorem inline (locals : List TxLocalBatch) (active : List (List SkbId)) :
    Preserves (fun w : World => Coherent locals active w.wg) Env.pollScheduledInline :=
  native locals active _ _ RxHistory.pollScheduledInline_erases (inline_observed locals active)

theorem irqExit (locals : List TxLocalBatch) (active : List (List SkbId)) :
    Preserves (fun w : World => Coherent locals active w.wg) Env.napiIrqExit :=
  native locals active _ _ RxHistory.napiIrqExit_erases (irqExit_observed locals active)

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Napi
