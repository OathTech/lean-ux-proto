import Leanux.Proofs.WG.Queues.DecryptStable
import Leanux.Proofs.WG.Queues.RxReservationPayment

/-! Conditional composition of the original decrypt-worker observer. Callback
relations retain their exact before/after ledger and journal cuts. The named
publication reservation survives IRQ until the actual source payment. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DecryptIteration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

abbrev Journal := List RxHistory.Event

def Stable (cs : Ledger) (loans : Reservations) (w : World) : Prop :=
  CarrierState cs loans w.wg ∧ StableRx cs w.wg

def Physical (w : World) : Prop :=
  ∃ epoch n h, NativeRxInv epoch (PtrRing.init n) h w.wg

/-- The relation can specify exact admitted/removed journal suffixes. It is
not replaced by an arbitrary existential final ledger. -/
def Advances (g : RxHistory.Obs Unit)
    (R : Ledger → Journal → World → Ledger → Journal → World → Prop) : Prop :=
  ∀ cs loans w h v k, Stable cs loans w → runPrefix g w h=(.ok ((),v),k) →
    ∃ ds, R cs h w ds k v ∧ Stable ds loans v

theorem bind_normal {E α β : Type} {w v : World} {h k : List E} {out : β} {g : PrefixM E α} {f : α → PrefixM E β}
    (hr : runPrefix (g >>= f) w h=(.ok (out,v),k)) :
    ∃ x mid journal, runPrefix g w h=(.ok (x,mid),journal) ∧
      runPrefix (f x) mid journal=(.ok (out,v),k) := by
  rw [runPrefix_bind] at hr
  cases hg : runPrefix g w h with
  | mk result journal =>
    cases result with
    | error e => simp [hg] at hr
    | ok pair =>
      rcases pair with ⟨x,mid⟩
      exact ⟨x,mid,journal,rfl,by simpa only [hg] using hr⟩

theorem native_normal {E α : Type} {w v : World} {h k : List E} {out : α} {g : PrefixM E α} {a : WG.M α}
    (erase : ErasesPrefix g (liftWG a))
    (hr : runPrefix g w h=(.ok (out,v),k)) :
    (a.run w.wg).run w.ambient=.ok ((out,v.wg),v.ambient) := by
  have raw : (liftWG a).run w=.ok (out,v) := by
    have eq := erase w h
    simpa only [hr] using eq.symm
  rw [liftWG_run] at raw
  cases native : (a.run w.wg).run w.ambient with
  | error e => simp only [native,Except.map] at raw; cases raw
  | ok pair =>
    rcases pair with ⟨⟨x,world⟩,ambient⟩
    simp only [native,Except.map] at raw
    cases raw
    rfl

/-- All native state conclusions are tied to the existing prepare journal. -/
theorem prepare_normal (hi : Stable cs loans w) (physical : Physical w)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h=(.ok (result,v),k)) :
    DecryptCarrier.Prepared cs loans result v.wg ∧ StableRx cs v.wg := by
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  have native := native_normal Origins.HistoryAdapters.prepare_erases hr
  exact ⟨DecryptCarrier.prepare_state hi.1 w.ambient v.ambient native,
    DecryptStable.prepare_stable hi.1 hi.2 ring w.ambient v.ambient native⟩

theorem payment_normal (hi : Stable cs (o::loans) w)
    (hr : runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some o.slot)))) w h=(.ok ((),v),k)) :
    Stable cs loans v := by
  have native := native_normal
    (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _))) hr
  exact reservation_payment_stable hi.1 hi.2 w.ambient v.ambient native


/-- The normal source path retains the callback relations and the actual
prepare/payment executions at their exact journal positions. -/
def NormalPath (softirq irq : RxHistory.Obs Unit)
    (RS RI : Ledger → Journal → World → Ledger → Journal → World → Prop)
    (cs : Ledger) (loans : Reservations) (w : World) (h : Journal)
    (result : Bool) (ds : Ledger) (v : World) (k : Journal) : Prop :=
  ∃ enteredLedger entered enteredHistory,
    runPrefix softirq w h=(.ok ((),entered),enteredHistory) ∧
    RS cs h w enteredLedger enteredHistory entered ∧
    if result then
      ∃ pid, ∃ o : Owner, ∃ prepared preparedHistory irqLedger irqWorld irqHistory paid paidHistory,
        runPrefix Origins.HistoryAdapters.prepare entered enteredHistory=(.ok (some pid,prepared),preparedHistory) ∧
        o.slot=pid ∧ Stable enteredLedger (o::loans) prepared ∧
        runPrefix irq prepared preparedHistory=(.ok ((),irqWorld),irqHistory) ∧
        RI enteredLedger preparedHistory prepared irqLedger irqHistory irqWorld ∧
        Stable irqLedger (o::loans) irqWorld ∧
        runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) irqWorld irqHistory=(.ok ((),paid),paidHistory) ∧
        Stable irqLedger loans paid ∧
        runPrefix softirq paid paidHistory=(.ok ((),v),k) ∧
        RS irqLedger paidHistory paid ds k v
    else ds=enteredLedger ∧
      runPrefix Origins.HistoryAdapters.prepare entered enteredHistory=(.ok (none,v),k)

/-- The callbacks may change the carrier ledger. IRQ retains the same named
publication reservation; the following native put discharges precisely it. -/
theorem step_normal (softirq irq : RxHistory.Obs Unit)
    (RS RI : Ledger → Journal → World → Ledger → Journal → World → Prop)
    (soft : Advances softirq RS) (interrupt : Advances irq RI)
    (softPhysical : ∀ w h v k, Physical w →
      runPrefix softirq w h=(.ok ((),v),k) → Physical v)
    (hi : Stable cs loans w) (physical : Physical w)
    (hr : runPrefix (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
      (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq) w h=(.ok (result,v),k)) :
    ∃ ds, Stable ds loans v ∧ NormalPath softirq irq RS RI cs loans w h result ds v k := by
  unfold RxWorkers.decryptWith at hr
  obtain ⟨u,entered,enteredHistory,hsoft,tail⟩ := bind_normal hr
  cases u
  obtain ⟨enteredLedger,relation,stableEntered⟩ := soft cs loans w h entered enteredHistory hi hsoft
  have enteredPhysical := softPhysical w h entered enteredHistory physical hsoft
  obtain ⟨preparedResult,prepared,preparedHistory,hprepare,tail⟩ := bind_normal tail
  have preparedState := prepare_normal stableEntered enteredPhysical hprepare
  cases preparedResult with
  | none =>
    cases tail
    exact ⟨enteredLedger,⟨preparedState.1,preparedState.2⟩,
      enteredLedger,entered,enteredHistory,hsoft,relation,rfl,hprepare⟩
  | some pid =>
    obtain ⟨o,slot,carrierPrepared⟩ := preparedState.1
    have stablePrepared : Stable enteredLedger (o::loans) prepared := ⟨carrierPrepared,preparedState.2⟩
    obtain ⟨u,irqWorld,irqHistory,hirq,tail⟩ := bind_normal tail
    cases u
    obtain ⟨irqLedger,irqRelation,stableIrq⟩ := interrupt enteredLedger (o::loans) prepared preparedHistory irqWorld irqHistory stablePrepared hirq
    obtain ⟨u,paid,paidHistory,hpay,tail⟩ := bind_normal tail
    cases u
    have stablePaid : Stable irqLedger loans paid := payment_normal stableIrq (slot ▸ hpay)
    obtain ⟨u,final,finalHistory,hfinal,hpure⟩ := bind_normal tail
    cases u
    cases hpure
    obtain ⟨ds,finalRelation,stableFinal⟩ := soft irqLedger loans paid paidHistory v k stablePaid hfinal
    exact ⟨ds,stableFinal,enteredLedger,entered,enteredHistory,hsoft,relation,
      pid,o,prepared,preparedHistory,irqLedger,irqWorld,irqHistory,paid,paidHistory,
      hprepare,slot,stablePrepared,hirq,irqRelation,stableIrq,hpay,stablePaid,hfinal,finalRelation⟩

/-- Every stopped prefix is the existing observer's prefix. This composition
requires only append contracts for the two actual callback arguments. -/
theorem step_appends (softirq irq : RxHistory.Obs Unit)
    (soft : Appends softirq) (interrupt : Appends irq) :
    Appends (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
      (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq) := by
  unfold RxWorkers.decryptWith
  apply soft.bind
  intro _
  apply (Appends.focus _ _ _).bind
  intro result
  cases result with
  | none => exact Appends.pure _
  | some pid =>
    apply interrupt.bind
    intro _
    apply (Appends.focus _ _ _).bind
    intro _
    exact soft.bind (fun _ => Appends.pure _)

/-- Exact original product execution, including its Stop value, is retained. -/
theorem step_erases (softirq irq : RxHistory.Obs Unit) (originalSoft originalIRQ : Leanux.M Unit)
    (soft : ErasesPrefix softirq originalSoft) (interrupt : ErasesPrefix irq originalIRQ) :
    ErasesPrefix (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
      (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq)
      (WG.decryptStep originalSoft originalIRQ) := by
  rw [←RxWorkers.decrypt_source]
  unfold RxWorkers.decryptWith RxWorkers.decryptSource
  apply erasesPrefix_bind soft
  intro _
  apply erasesPrefix_bind Origins.HistoryAdapters.prepare_erases
  intro result
  cases result with
  | none => exact erasesPrefix_pure _
  | some pid =>
    exact erasesPrefix_bind interrupt (fun _ =>
      erasesPrefix_bind (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _)))
        (fun _ => erasesPrefix_bind soft (fun _ => erasesPrefix_pure _)))


/-- The scheduler continuation is tied to the same completed step, rather
than supplied as a statement about the final iteration endpoint. -/
def IterationPath (softirq irq : RxHistory.Obs Unit) (afterItem : RxHistory.Obs Bool)
    (RS RI : Ledger → Journal → World → Ledger → Journal → World → Prop)
    (RA : Ledger → Journal → World → Bool → Ledger → Journal → World → Prop)
    (cs : Ledger) (loans : Reservations) (w : World) (h : Journal)
    (result : IterResult) (ds : Ledger) (v : World) (k : Journal) : Prop :=
  ∃ more middleLedger middle middleHistory,
    runPrefix (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
      (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq) w h=
      (.ok (more,middle),middleHistory) ∧
    NormalPath softirq irq RS RI cs loans w h more middleLedger middle middleHistory ∧
    Stable middleLedger loans middle ∧
    if more then
      ∃ yielded, runPrefix afterItem middle middleHistory=(.ok (yielded,v),k) ∧
        RA middleLedger middleHistory middle yielded ds k v ∧
        result=(if yielded then .yielded else .continued)
    else ds=middleLedger ∧ v=middle ∧ k=middleHistory ∧ result=.ended

theorem iteration_normal (softirq irq : RxHistory.Obs Unit) (afterItem : RxHistory.Obs Bool)
    (RS RI : Ledger → Journal → World → Ledger → Journal → World → Prop)
    (RA : Ledger → Journal → World → Bool → Ledger → Journal → World → Prop)
    (soft : Advances softirq RS) (interrupt : Advances irq RI)
    (softPhysical : ∀ w h v k, Physical w →
      runPrefix softirq w h=(.ok ((),v),k) → Physical v)
    (after : ∀ cs loans w h v k more, Stable cs loans w →
      runPrefix afterItem w h=(.ok (more,v),k) →
      ∃ ds, RA cs h w more ds k v ∧ Stable ds loans v)
    (hi : Stable cs loans w) (physical : Physical w)
    (hr : runPrefix (workerIterPrefix .decryptWorker none
      (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
        (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq)
      afterItem) w h=(.ok (result,v),k)) :
    ∃ ds, Stable ds loans v ∧ IterationPath softirq irq afterItem RS RI RA cs loans w h result ds v k := by
  unfold workerIterPrefix at hr
  obtain ⟨more,middle,middleHistory,stepRun,tail⟩ := bind_normal hr
  obtain ⟨middleLedger,middleStable,path⟩ := step_normal softirq irq RS RI soft interrupt softPhysical hi physical stepRun
  cases more with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact ⟨middleLedger,middleStable,false,middleLedger,v,k,stepRun,path,middleStable,rfl,rfl,rfl,rfl⟩
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,final,finalHistory,afterRun,hpure⟩ := bind_normal tail
    cases hpure
    obtain ⟨ds,afterRelation,finalStable⟩ := after middleLedger loans middle middleHistory v k yielded middleStable afterRun
    exact ⟨ds,finalStable,true,middleLedger,middle,middleHistory,stepRun,path,middleStable,
      yielded,afterRun,afterRelation,rfl⟩

theorem iteration_appends (softirq irq : RxHistory.Obs Unit) (afterItem : RxHistory.Obs Bool)
    (soft : Appends softirq) (interrupt : Appends irq) (after : Appends afterItem) :
    Appends (workerIterPrefix .decryptWorker none
      (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
        (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq)
      afterItem) := by
  unfold workerIterPrefix
  apply (step_appends softirq irq soft interrupt).bind
  intro more
  cases more with
  | false => exact Appends.pure _
  | true => exact after.bind (fun _ => Appends.pure _)

theorem iteration_erases (softirq irq : RxHistory.Obs Unit) (afterItem : RxHistory.Obs Bool)
    (originalSoft originalIRQ : Leanux.M Unit) (needResched : Leanux.M Bool)
    (soft : ErasesPrefix softirq originalSoft) (interrupt : ErasesPrefix irq originalIRQ)
    (after : ErasesPrefix afterItem (do branch .decWorkerNeedResched (←needResched))) :
    ErasesPrefix (workerIterPrefix .decryptWorker none
      (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
        (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq)
      afterItem) (WG.decryptIter originalSoft originalIRQ needResched) :=
  workerIterPrefix_erases .decryptWorker none (step_erases softirq irq originalSoft originalIRQ soft interrupt) after

end Leanux.Proofs.WG.Queues.RxCredits.DecryptIteration
