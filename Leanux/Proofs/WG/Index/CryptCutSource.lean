import Leanux.Proofs.WG.Index.CryptPreparationSource
import Leanux.Proofs.WG.Index.CryptCutModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem cut_of_aux {initial : Ledger} {loans : Reservations}
    {before h : List RxHistory.Event} {w : World}
    (entry : Reached.Aux initial loans before h w) : Cut initial loans before h w :=
  ⟨entry.1.1.1,entry.1.2.1,entry.1.2.2,entry.2.1,entry.2.2⟩

theorem prepare_cut {initial : Ledger} {loans : Reservations}
    {before h k : List RxHistory.Event} {w v : World} {result : Option PeerId}
    (entry : Cut initial loans before h w) (physical : DecryptIteration.Physical w)
    (run : runPrefix Origins.HistoryAdapters.prepare w h=(.ok (result,v),k)) :
    match result with
    | none => Cut initial loans before k v
    | some pid => ∃o : Owner,o.slot=pid ∧ Cut initial (o::loans) before k v := by
  have holders := HolderDecryptHistory.prepare_at entry.1 physical run
  have owners := (OwnerPrepare.prepare w h entry.2.1).choose_spec.2.2
  have slots := (CurrentSlots.prepare_observed w h entry.2.2.1).choose_spec.2.2
  have base := (BaseCoherence.prepare_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at owners slots base
  have native := DecryptIteration.native_normal Origins.HistoryAdapters.prepare_erases run
  have core := (hoare_iff_run_ambient _ _ _).mp prepare_core
    w.wg w.ambient result v.wg v.ambient entry.2.2.2.2 native
  have rest : OwnerChecks.Inv k v ∧ CurrentSlots.Inv v.wg ∧ BaseCoherence.Inv v.wg ∧ Reached.Core v.wg :=
    ⟨owners,slots,BaseCoherence.transport entry.2.2.2.1 base,core⟩
  cases result with
  | none => exact ⟨holders,rest⟩
  | some pid =>
    obtain ⟨o,slot,funded⟩ := holders
    exact ⟨o,slot,funded,rest⟩

theorem payment_cut {initial : Ledger} {loans : Reservations} {paid : Owner}
    {before h k : List RxHistory.Event} {w v : World}
    (entry : Cut initial (paid::loans) before h w)
    (run : runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some paid.slot))))
      w h=(.ok ((),v),k)) : Cut initial loans before k v := by
  have account := HolderDecryptHistory.payment_at entry.1 run
  have native := DecryptIteration.native_normal
    (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases (some paid.slot)))) run
  obtain ⟨suffix,_,boundary⟩ := entry.1
  have post := Reached.peerPut_boundary_core
    (remaining initial (NapiCarrier.removedPackets suffix)) paid loans
    w.wg w.ambient () v.wg v.ambient
    ⟨⟨boundary,entry.2.2.2.1,HolderAuxiliary.owner_configured entry.2.1⟩,entry.2.2.2.2⟩ native
  have owners := ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCryptWorkers.«0».Leanux.Proofs.WG.OwnerCryptWorkers.pay)
    paid.slot w h entry.2.1).choose_spec.2.2
  simp only [run] at owners
  exact ⟨account,owners,(hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.peerPut_preserves (some paid.slot)) w.wg w.ambient () v.wg v.ambient
    entry.2.2.1 native,post.1.2.1,post.2⟩

theorem softirq_cut
    (ready : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiSoftirq)
    {initial : Ledger} {loans : Reservations}
    {before h k : List RxHistory.Event} {w v : World}
    (entry : Cut initial loans before h w)
    (run : runPrefix RxHistory.napiSoftirq w h=(.ok ((),v),k)) :
    Cut initial loans before k v := by
  have owners := (OwnerWorkers.napiSoftirq w h entry.2.1).choose_spec.2.2
  have base := (BaseCoherence.softirq_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at owners base
  have state := (hoare_iff_run _ _ _).mp ready w () v
    ⟨entry.2.2.1,entry.2.2.2.2⟩
    ((RxHistory.napiSoftirq_erases w h).symm.trans (congrArg Prod.fst run))
  exact ⟨HolderDecryptHistory.softirq_at entry.1 run,owners,state.1,
    BaseCoherence.transport entry.2.2.2.1 base,state.2⟩

theorem irq_cut
    (ready : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiIrqExit)
    {initial : Ledger} {loans : Reservations}
    {before h k : List RxHistory.Event} {w v : World}
    (entry : Cut initial loans before h w)
    (run : runPrefix RxHistory.napiIrqExit w h=(.ok ((),v),k)) :
    Cut initial loans before k v := by
  have owners := (OwnerWorkers.napiIrqExit w h entry.2.1).choose_spec.2.2
  have base := (BaseCoherence.irqExit_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at owners base
  have state := (hoare_iff_run _ _ _).mp ready w () v
    ⟨entry.2.2.1,entry.2.2.2.2⟩
    ((RxHistory.napiIrqExit_erases w h).symm.trans (congrArg Prod.fst run))
  exact ⟨HolderDecryptHistory.irq_at entry.1 run,owners,state.1,
    BaseCoherence.transport entry.2.2.2.1 base,state.2⟩

theorem decryptStep_cut
    (soft : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiSoftirq)
    (irq : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiIrqExit)
    {initial : Ledger} {loans : Reservations}
    {before h k : List RxHistory.Event} {w v : World} {result : Bool}
    (entry : Cut initial loans before h w) (physical : DecryptIteration.Physical w)
    (run : runPrefix RxHistory.decryptStep w h=(.ok (result,v),k)) :
    Cut initial loans before k v := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith at run
  obtain ⟨u,entered,enteredHistory,hsoft,tail⟩ := DecryptIteration.bind_normal run
  cases u
  have enteredState := softirq_cut soft entry hsoft
  have enteredPhysical := DecryptConcrete.softirq_physical physical hsoft
  obtain ⟨preparedResult,prepared,preparedHistory,hprepare,tail⟩ := DecryptIteration.bind_normal tail
  have preparedState := prepare_cut enteredState enteredPhysical hprepare
  cases preparedResult with
  | none => cases tail; exact preparedState
  | some pid =>
    obtain ⟨o,slot,preparedState⟩ := preparedState
    obtain ⟨u,irqWorld,irqHistory,hirq,tail⟩ := DecryptIteration.bind_normal tail
    cases u
    have irqState := irq_cut irq preparedState hirq
    obtain ⟨u,paid,paidHistory,hpay,tail⟩ := DecryptIteration.bind_normal tail
    cases u
    have paidState := payment_cut irqState (slot ▸ hpay)
    obtain ⟨u,final,finalHistory,hfinal,hpure⟩ := DecryptIteration.bind_normal tail
    cases u
    cases hpure
    exact softirq_cut soft paidState hfinal

theorem decryptIteration_core
    (soft : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiSoftirq)
    (irq : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiIrqExit)
    {initial : Ledger} {loans : Reservations}
    {before h k : List RxHistory.Event} {w v : World} {result : IterResult}
    (entry : Reached.Aux initial loans before h w)
    (run : runPrefix RxHistory.decryptIteration w h=(.ok (result,v),k)) :
    BaseCoherence.Inv v.wg ∧ Reached.Core v.wg := by
  unfold RxHistory.decryptIteration workerIterPrefix at run
  obtain ⟨more,middle,middleHistory,stepRun,tail⟩ := DecryptIteration.bind_normal run
  have middleState := decryptStep_cut soft irq (cut_of_aux entry) entry.1.1.2 stepRun
  cases more with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact middleState.2.2.2
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,final,finalHistory,afterRun,hpure⟩ := DecryptIteration.bind_normal tail
    cases hpure
    obtain ⟨old,history,holders,funded,stable⟩ := middleState.1
    obtain ⟨same,_⟩ := DecryptConcrete.after_normal ⟨funded.carriers,stable⟩ afterRun
    have device : v.wg.dev=middle.wg.dev :=
      congrArg (fun p : ProductStore43 => p.2.2.2.dev) same.2.2
    exact ⟨BaseCoherence.transport middleState.2.2.2.1
      (congrArg (fun d : Option Device => BaseCoherence.view {dev:=d}) device),
      Reached.core_device device middleState.2.2.2.2⟩

theorem decrypt_observed
    (soft : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiSoftirq)
    (irq : Preserves (fun w : World => TimerCore.Ready w.wg) Env.napiIrqExit)
    (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.decryptIteration := by
  apply Reached.aux_pair _ initial loans before
    (HolderAuxScheduler.decrypt_preserves initial loans before)
  intro w h entry result v run
  exact decryptIteration_core soft irq entry (Prod.ext run rfl)

end Leanux.Proofs.WG.Index.CryptCore
