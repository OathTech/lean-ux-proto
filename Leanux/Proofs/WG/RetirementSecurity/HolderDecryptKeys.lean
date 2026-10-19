import Leanux.Proofs.WG.RetirementSecurity.HolderDecryptPreparation
import Leanux.Proofs.WG.Queues.HolderDecryptHistory

/-! Exact key credit survives the original decrypt iteration, including the
actual pre-poll, publication loan, IRQ callback, peer payment and final poll.
The peer loan is separately funded throughout, while key ownership follows
the native selected RX occurrences and publication bookkeeping. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDecryptKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DecryptIteration (Physical bind_normal)
open HolderNapiKeys (Inv)

theorem prepare_at (entry : Inv sessions locals active temporary initial loans before h w)
    (physical : Physical w)
    (run : runPrefix Origins.HistoryAdapters.prepare w h=(.ok (result,v),k)) :
    match result with
    | none=>Inv sessions locals active temporary initial loans before k v
    | some pid=>∃o:Owner,o.slot=pid ∧ Inv sessions locals active temporary initial (o::loans) before k v := by
  have original := DecryptIteration.native_normal Origins.HistoryAdapters.prepare_erases run
  have keys := (hoare_iff_run_ambient _ _ _).mp prepare_keys w.wg w.ambient result v.wg v.ambient entry.2.1 original
  have support := (hoare_iff_run_ambient _ _ _).mp prepare_support w.wg w.ambient result v.wg v.ambient entry.2.2 original
  have old := HolderDecryptHistory.prepare_at entry.1 physical run
  cases result with
  | none=>exact ⟨old,keys,support⟩
  | some pid=>obtain ⟨o,slot,state⟩:=old; exact ⟨o,slot,state,keys,support⟩

theorem payment_at (entry : Inv sessions locals active temporary initial (o::loans) before h w)
    (run : runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some o.slot)))) w h=(.ok ((),v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  obtain ⟨suffix,history,holders,funded,stable⟩ := entry.1
  have anchors : SlotPeerReferences holders loans w.wg := by
    intro d pid p device stored slots
    exact List.mem_append_left _ (live_peer_base_reference funded entry.2.2.2.2.1 entry.2.2.2.1.1
      device stored (entry.2.2.2.2.2 pid p (by simp [peerAt,device,stored]) (by simp) slots))
  have ready := (selected_loan_peer_release_funded funded.carriers anchors).ready
  have original := DecryptIteration.native_normal
    (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _))) run
  exact ⟨HolderDecryptHistory.payment_at entry.1 run,
    entry.2.1.peer_put ready w.ambient v.ambient original,
    (hoare_iff_run_ambient _ _ _).mp (HolderPoll.peer_put (some o.slot))
      w.wg w.ambient () v.wg v.ambient entry.2.2 original⟩

theorem softirq_at (entry : Inv sessions locals active temporary initial loans before h w)
    (run : runPrefix RxHistory.napiSoftirq w h=(.ok ((),v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  have post := (HolderNapiKeys.softirq w h entry).choose_spec.2.2
  simpa only [run] using post

theorem irq_at (entry : Inv sessions locals active temporary initial loans before h w)
    (run : runPrefix RxHistory.napiIrqExit w h=(.ok ((),v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  have post := (HolderNapiKeys.irq w h entry).choose_spec.2.2
  simpa only [run] using post

theorem step_normal (entry : Inv sessions locals active temporary initial loans before h w)
    (physical : Physical w)
    (run : runPrefix RxHistory.decryptStep w h=(.ok (result,v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith at run
  obtain ⟨u,entered,enteredHistory,softirq,tail⟩ := bind_normal run
  cases u
  have enteredState := softirq_at entry softirq
  have enteredPhysical := DecryptConcrete.softirq_physical physical softirq
  obtain ⟨preparedResult,prepared,preparedHistory,prepare,tail⟩ := bind_normal tail
  have preparedState := prepare_at enteredState enteredPhysical prepare
  cases preparedResult with
  | none=>cases tail; exact preparedState
  | some pid=>
    obtain ⟨o,slot,preparedState⟩ := preparedState
    obtain ⟨u,irqWorld,irqHistory,irq,tail⟩ := bind_normal tail
    cases u
    have irqState := irq_at preparedState irq
    obtain ⟨u,paid,paidHistory,payment,tail⟩ := bind_normal tail
    cases u
    have paidState := payment_at irqState (slot ▸ payment)
    obtain ⟨u,final,finalHistory,last,finish⟩ := bind_normal tail
    cases u
    cases finish
    exact softirq_at paidState last

theorem after_at (entry : Inv sessions locals active temporary initial loans before h w)
    (run : runPrefix DecryptConcrete.afterItem w h=(.ok (result,v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  obtain ⟨old,history,holders,funded,stable⟩ := entry.1
  obtain ⟨same,_⟩ := DecryptConcrete.after_normal ⟨funded.carriers,stable⟩ run
  rw [same.2.1]
  exact HolderNapiKeys.store entry same.2.2

theorem iteration_normal (entry : Inv sessions locals active temporary initial loans before h w)
    (physical : Physical w)
    (run : runPrefix RxHistory.decryptIteration w h=(.ok (result,v),k)) :
    Inv sessions locals active temporary initial loans before k v := by
  unfold RxHistory.decryptIteration workerIterPrefix at run
  obtain ⟨more,middle,middleHistory,step,tail⟩ := bind_normal run
  have middleState := step_normal entry physical step
  cases more with
  | false=>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact middleState
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,final,finalHistory,after,finish⟩ := bind_normal tail
    cases finish
    exact after_at middleState after

end Leanux.Proofs.WG.RetirementSecurity.HolderDecryptKeys
