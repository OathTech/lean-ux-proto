import Leanux.Proofs.WG.Queues.HolderDecrypt

/-! The actual decrypt worker carries the complete holder account through its
NAPI callbacks and the temporary publication reference. Its persistent journal
determines the remaining RX ledger, including across earlier poll calls. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDecryptHistory
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
open DecryptIteration (Physical Journal bind_normal)
open NapiCarrier (removed removedPackets)

/-- An observer with no removal record extends the same fixed accounting cut. -/
theorem quiet_cut {action : RxHistory.Obs α} (ha : Appends action)
    (quiet : HistoryFrame removed action) (history : h = before ++ old)
    (run : runPrefix action w h = (.ok (x,v),k))
    (post : Boundary (remaining initial (removedPackets old)) loans v.wg) :
    HolderNapi.At initial loans before k v := by
  obtain ⟨extra,extraEq⟩ := ha w h
  have tail : k = h ++ extra := by simpa only [run] using extraEq
  have empty : removedPackets extra = [] := by
    have same := quiet w h
    change removedPackets (runPrefix action w h).2 = removedPackets h at same
    rw [extraEq] at same
    exact List.append_cancel_left (by simpa only [removedPackets,List.filterMap_append,List.append_nil] using same)
  refine ⟨old ++ extra,by rw [tail,history,List.append_assoc],?_⟩
  simp only [removedPackets,List.filterMap_append]
  change Boundary (remaining initial (removedPackets old ++ removedPackets extra)) loans v.wg
  rw [empty,List.append_nil]
  exact post

theorem prepare_quiet : HistoryFrame removed Origins.HistoryAdapters.prepare := by
  intro w h
  unfold Origins.HistoryAdapters.prepare Origins.HistoryAdapters.focus
  exact focusPrefix_other Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode removed
    (fun e => by cases e <;> rfl) _ w h

theorem prepare_at (hi : HolderNapi.At initial loans before h w) (physical : Physical w)
    (run : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (result,v),k)) :
    match result with
    | none => HolderNapi.At initial loans before k v
    | some pid => ∃ o : Owner, o.slot = pid ∧ HolderNapi.At initial (o :: loans) before k v := by
  obtain ⟨old,history,stable⟩ := hi
  have prepared := HolderDecrypt.prepare_normal stable physical run
  cases result with
  | none => exact quiet_cut (Appends.focus _ _ _) prepare_quiet history run prepared
  | some pid =>
    obtain ⟨o,slot,funded⟩ := prepared
    exact ⟨o,slot,quiet_cut (Appends.focus _ _ _) prepare_quiet history run funded⟩

theorem payment_at (hi : HolderNapi.At initial (o :: loans) before h w)
    (run : runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some o.slot)))) w h = (.ok ((),v),k)) :
    HolderNapi.At initial loans before k v := by
  obtain ⟨old,history,stable⟩ := hi
  apply quiet_cut (Appends.focus _ _ _) _ history run (HolderDecrypt.payment_normal stable run)
  intro w h
  exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent removed (fun _ => rfl) _ w h

theorem softirq_at (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix RxHistory.napiSoftirq w h = (.ok ((),v),k)) :
    HolderNapi.At initial loans before k v := by
  have post := (HolderNapi.softirq_preserves initial loans before w h hi).choose_spec.2.2
  simpa only [run] using post

theorem irq_at (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix RxHistory.napiIrqExit w h = (.ok ((),v),k)) :
    HolderNapi.At initial loans before k v := by
  have post := (HolderNapi.irq_preserves initial loans before w h hi).choose_spec.2.2
  simpa only [run] using post

/-- The same concrete calls carry one publication loan from prepare through
IRQ to payment. Callback acquisitions become durable holders at their source. -/
theorem step_normal (hi : HolderNapi.At initial loans before h w) (physical : Physical w)
    (run : runPrefix RxHistory.decryptStep w h = (.ok (result,v),k)) :
    HolderNapi.At initial loans before k v := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith at run
  obtain ⟨u,entered,enteredHistory,hsoft,tail⟩ := bind_normal run
  cases u
  have enteredState := softirq_at hi hsoft
  have enteredPhysical := DecryptConcrete.softirq_physical physical hsoft
  obtain ⟨preparedResult,prepared,preparedHistory,hprepare,tail⟩ := bind_normal tail
  have preparedState := prepare_at enteredState enteredPhysical hprepare
  cases preparedResult with
  | none => cases tail; exact preparedState
  | some pid =>
    obtain ⟨o,slot,preparedState⟩ := preparedState
    obtain ⟨u,irqWorld,irqHistory,hirq,tail⟩ := bind_normal tail
    cases u
    have irqState := irq_at preparedState hirq
    obtain ⟨u,paid,paidHistory,hpay,tail⟩ := bind_normal tail
    cases u
    have paidState := payment_at irqState (slot ▸ hpay)
    obtain ⟨u,final,finalHistory,hfinal,hpure⟩ := bind_normal tail
    cases u
    cases hpure
    exact softirq_at paidState hfinal

theorem after_at (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix DecryptConcrete.afterItem w h = (.ok (result,v),k)) :
    HolderNapi.At initial loans before k v := by
  obtain ⟨old,history,holders,funded,stable⟩ := hi
  obtain ⟨same,_⟩ := DecryptConcrete.after_normal ⟨funded.carriers,stable⟩ run
  rw [same.2.1]
  exact HolderNapi.store ⟨old,history,holders,funded,stable⟩ same.2.2

/-- One actual iteration retains the fixed history cut on its ended, continued
and yielded outcomes; rescheduling introduces no fabricated state. -/
theorem iteration_normal (hi : HolderNapi.At initial loans before h w) (physical : Physical w)
    (run : runPrefix RxHistory.decryptIteration w h = (.ok (result,v),k)) :
    HolderNapi.At initial loans before k v := by
  unfold RxHistory.decryptIteration workerIterPrefix at run
  obtain ⟨more,middle,middleHistory,stepRun,tail⟩ := bind_normal run
  have middleState := step_normal hi physical stepRun
  cases more with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact middleState
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,final,finalHistory,afterRun,hpure⟩ := bind_normal tail
    cases hpure
    exact after_at middleState afterRun

/-- The fresh persistent journal suffix determines the returned carrier ledger.
The original physical-ring observer supplies the next physical witness. -/
theorem native_normal (hi : Boundary cs loans w.wg) (physical : Physical w)
    (run : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) (h : Journal) :
    let k := (runPrefix RxHistory.decryptIteration w h).2
    (∃ suffix, k = h ++ suffix ∧ Boundary (remaining cs (removedPackets suffix)) loans v.wg) ∧
      Physical v := by
  have observed : runPrefix RxHistory.decryptIteration w h =
      (.ok (result,v),(runPrefix RxHistory.decryptIteration w h).2) :=
    Prod.ext ((RxHistory.decryptIteration_erases w h).trans run) rfl
  have post := iteration_normal (HolderNapi.at_start hi h) physical observed
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  exact ⟨post,epoch,n,_,DecryptConcrete.ring_normal ring run⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderDecryptHistory
