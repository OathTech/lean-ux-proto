import Leanux.Proofs.WG.Queues.NapiCarrier
import Leanux.Proofs.WG.Queues.RxRingNapi
import Leanux.Proofs.WG.Queues.RxRingWorker

/-! Concrete decrypt iteration with the original persistent receive observer.
The NAPI cuts retain their fresh-removal relation, the source-owned publication
loan is paid after IRQ, and rescheduling changes neither ledger nor journal.
The physical ring witness is separate from the persistent receive journal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DecryptConcrete
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DecryptIteration

/-- The literal continuation already used by RxHistory.decryptIteration. -/
def afterItem : RxHistory.Obs Bool := do
  liftPrefix (branch .decWorkerNeedResched (← liftPrefix (Env.condResched .decryptWorker)))

/-- The reschedule result is recorded; its ledger and observer journal do not
change. Ambient scheduling records may be consumed. -/
def Rescheduled (cs : Ledger) (h : Journal) (w : World) (_ : Bool)
    (ds : Ledger) (k : Journal) (v : World) : Prop :=
  ds = cs ∧ k = h ∧ productStoreView v = productStoreView w

abbrev Path := IterationPath RxHistory.napiSoftirq RxHistory.napiIrqExit afterItem
  NapiCarrier.Removed NapiCarrier.Removed Rescheduled

private theorem stable_store (hi : Stable cs loans w)
    (same : productStoreView v = productStoreView w) : Stable cs loans v := by
  obtain ⟨suffix,history,kept⟩ := NapiCarrier.store (NapiCarrier.at_start hi ([] : Journal)) same
  have empty : suffix = [] := by simpa only [List.nil_append] using history.symm
  have unchanged : remaining cs [] = cs := List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [empty,NapiCarrier.removedPackets,List.filterMap_nil,unchanged] using kept

theorem after_normal (hi : Stable cs loans w)
    (hr : runPrefix afterItem w h = (.ok (result,v),k)) :
    Rescheduled cs h w result cs k v ∧ Stable cs loans v := by
  unfold afterItem at hr
  obtain ⟨need,mid,j,cond,decision⟩ := bind_normal hr
  simp only [runPrefix_lift,Prod.mk.injEq] at cond decision
  obtain ⟨cond,rfl⟩ := cond
  obtain ⟨decision,rfl⟩ := decision
  have hc := (ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel .decryptWorker) w need mid cond
  have ambient : SameProductStore (branch .decWorkerNeedResched need : Leanux.M Bool) := by
    intro initial
    exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched need) _ (fun _ _ h => h)
  have hb := (ProjectedAction.iff_run _ _ _).mp ambient mid result v decision
  exact ⟨⟨rfl,rfl,hb.trans hc⟩,stable_store hi (hb.trans hc)⟩

theorem softirq_physical (physical : Physical w)
    (hr : runPrefix RxHistory.napiSoftirq w h = (.ok ((),v),k)) : Physical v := by
  obtain ⟨epoch,n,ringHistory,ring,refined,cell⟩ := physical
  have raw : Env.napiSoftirq.run w = .ok ((),v) :=
    (RxHistory.napiSoftirq_erases w h).symm.trans (congrArg Prod.fst hr)
  have same := (ProjectedAction.iff_run _ _ _).mp RxRing.napiSoftirq_cell w () v raw
  exact ⟨epoch,n,ringHistory,ring,refined,same.trans cell⟩

/-- Every cut is the original observer's actual normal run. No callback
contract remains as an external premise. -/
theorem normal (hi : Stable cs loans w) (physical : Physical w)
    (hr : runPrefix RxHistory.decryptIteration w h = (.ok (result,v),k)) :
    ∃ ds, Stable ds loans v ∧ Path cs loans w h result ds v k := by
  exact iteration_normal RxHistory.napiSoftirq RxHistory.napiIrqExit afterItem
    NapiCarrier.Removed NapiCarrier.Removed Rescheduled
    NapiCarrier.softirq_advances NapiCarrier.irq_advances
    (fun _ _ _ _ => softirq_physical)
    (fun cs loans w h v k result hi hr => ⟨cs,after_normal hi hr⟩)
    hi physical hr

/-- The existing physical-ring observer follows this same raw execution.
Its journal is retained explicitly, separately from the receive journal. -/
theorem ring_normal (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg)
    (hr : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) :
    NativeRxInv epoch (PtrRing.init n)
      (runPrefix (RxRing.iter (liftPrefix Env.napiSoftirq) (liftPrefix Env.napiIrqExit)
        (liftPrefix (Env.condResched .decryptWorker))) w ringHistory).2 v.wg := by
  have resched : SameView RxRing.cell (Env.condResched .decryptWorker) :=
    (condResched_sameKernel .decryptWorker).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue))
      RxRing.cell (fun _ => rfl)
  have contract := RxRing.iter_preserves (deviceIndex := epoch) (initial := PtrRing.init n)
    (RxRing.lift_frame RxRing.napiSoftirq_cell)
    (RxRing.lift_frame RxRing.napiIrqExit_cell) (RxRing.lift_frame resched)
  have erase := RxRing.iter_erases (erasesPrefix_lift Env.napiSoftirq)
    (erasesPrefix_lift Env.napiIrqExit) (erasesPrefix_lift (Env.condResched .decryptWorker))
  have run := (erase w ringHistory).trans hr
  have post := (contract w ringHistory physical).choose_spec.2.2
  rw [run] at post
  obtain ⟨ring,refined,cell⟩ := post
  exact ⟨ring,refined,cell⟩

/-- Normal completion restores both funded stable carriers and a physical
ring witness, together with the same concrete receive-journal path. -/
theorem normal_physical (hi : Stable cs loans w) (physical : Physical w)
    (hr : runPrefix RxHistory.decryptIteration w h = (.ok (result,v),k)) :
    ∃ ds, Stable ds loans v ∧ Physical v ∧ Path cs loans w h result ds v k := by
  obtain ⟨ds,stable,path⟩ := normal hi physical hr
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  have raw : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v) :=
    (RxHistory.decryptIteration_erases w h).symm.trans (congrArg Prod.fst hr)
  exact ⟨ds,stable,⟨epoch,n,_,ring_normal ring raw⟩,path⟩

/-- The native caller has the exact same normal endpoint and persistent
journal; the latter is computed by the unchanged observer on this input. -/
theorem native_normal (hi : Stable cs loans w) (physical : Physical w)
    (hr : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) (h : Journal) :
    let k := (runPrefix RxHistory.decryptIteration w h).2
    ∃ ds, Stable ds loans v ∧ Physical v ∧ Path cs loans w h result ds v k := by
  have run : runPrefix RxHistory.decryptIteration w h =
      (.ok (result,v),(runPrefix RxHistory.decryptIteration w h).2) :=
    Prod.ext ((RxHistory.decryptIteration_erases w h).trans hr) rfl
  exact normal_physical hi physical run

end Leanux.Proofs.WG.Queues.RxCredits.DecryptConcrete
