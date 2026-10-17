import Leanux.Proofs.WG.Queues.AdmissionAuxiliary

/-! The real NET_RX section around a single receive occurrence. Section
markers remain in the actual Ambient stream, and no journal is fabricated
when the start, body or stop fails. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionSection
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def enter : RxHistory.Obs Unit := do
  _ ← liftPrefix (hidden (.sectionStart .netRx))
  liftPrefix (modifyAmbient fun s => {s with netRxSection:=s.netRxSections})

def leave : RxHistory.Obs Unit := do
  liftPrefix (modifyAmbient fun s => {s with netRxSection:=0})
  _ ← liftPrefix (hidden (.sectionStop .netRx))

theorem source_factor (msg src) :
    runWorkerPrefix .netRx (AdmissionCaller.receive msg src) = (do
      enter
      AdmissionCaller.receive msg src
      leave) := by
  simp only [runWorkerPrefix,enter,leave,bind_assoc]
  rfl

private theorem ambient (action : AmbientM α) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (liftPrefix (monadLift action : Leanux.M α)) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => HolderAuxiliary.store hi same)
    (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem enter_preserves : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe enter := by
  unfold enter
  exact PrefixPreserves.bind (ambient _) (fun _ => ambient _)

theorem leave_preserves : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe leave := by
  unfold leave
  exact PrefixPreserves.bind (ambient _) (fun _ =>
    PrefixPreserves.bind (ambient _) (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2.1.safe) ()))

theorem enter_history (w : World) (h : List RxHistory.Event) : (runPrefix enter w h).2=h := by
  have frame : HistoryFrame some enter := by
    unfold enter
    exact (HistoryFrame.lift _ _).bind (fun _ => HistoryFrame.lift _ _)
  simpa only [List.filterMap_some] using frame w h

theorem leave_history (w : World) (h : List RxHistory.Event) : (runPrefix leave w h).2=h := by
  have frame : HistoryFrame some leave := by
    unfold leave
    exact (HistoryFrame.lift _ _).bind (fun _ =>
      (HistoryFrame.lift _ _).bind (fun _ => HistoryFrame.pure _ _))
  simpa only [List.filterMap_some] using frame w h

/-- The exact section entry and exit surround the selected old-observer
receive occurrence. The relation contains executions, not a funded poststate. -/
def Step (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : World) (h k : List RxHistory.Event) : Prop :=
  ∃ u t, runPrefix enter w h=(.ok ((),u),h) ∧
    AdmissionCaller.Step cs next msg src u t h k ∧
    runPrefix leave t k=(.ok ((),v),k)

theorem normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) w h=(.ok ((),v),k)) :
    ∃ prior next, h=before++prior ∧
      Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
      HolderAuxiliary.Inv next loans k k v := by
  rw [source_factor] at run
  obtain ⟨x,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  cases x
  have same : j=h := by simpa only [start] using enter_history w h
  subst j
  have atStart := (enter_preserves w h hi).choose_spec.2.2
  rw [start] at atStart
  obtain ⟨x,t,l,body,stop⟩ := DecryptIteration.bind_normal tail
  cases x
  have same : k=l := by simpa only [stop] using leave_history t l
  subst l
  obtain ⟨prior,next,old,step,atEnd⟩ := AdmissionAuxiliary.receive_rebase atStart body
  have after := (leave_preserves t k atEnd).choose_spec.2.2
  rw [stop] at after
  exact ⟨prior,next,old,⟨u,t,start,step,stop⟩,after⟩

theorem Step.source (step : Step cs next msg src w v h k) :
    runPrefix (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) w h=(.ok ((),v),k) := by
  obtain ⟨u,t,start,body,stop⟩ := step
  rw [source_factor]
  simp only [runPrefix_bind,start,body.1,stop]

theorem Step.appends (step : Step cs next msg src w v h k) : ∃ suffix,k=h++suffix := by
  obtain ⟨u,t,_,body,_⟩ := step
  exact AdmissionCaller.step_appends body

theorem Step.unique (left : Step cs next msg src w v h k)
    (right : Step cs other msg src w v h k) : next=other := by
  obtain ⟨u,t,start,body,_⟩ := left
  obtain ⟨u',t',start',body',_⟩ := right
  rw [start] at start'
  obtain ⟨⟨_,rfl⟩,_⟩ := start'
  have same := body.1.symm.trans body'.1
  obtain ⟨⟨_,rfl⟩,_⟩ := same
  exact AdmissionCaller.step_unique body body'

/-- Even if a section marker or the body stops, the original observer's
reached journal is retained and owner-safe. Dynamic funding is concluded
only when the section actually returns normally. -/
theorem ensures (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (msg src) :
    PrefixEnsures (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (runWorkerPrefix .netRx (AdmissionCaller.receive msg src))
      (fun _ k v => ∃ prior next, ∃ w h, h=before++prior ∧
        Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
        HolderAuxiliary.Inv next loans k k v) := by
  have owner : OwnerChecks.Preserves (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) :=
    runWorkerPrefix_preserves (fun _ _ hi => hi.safe)
      (fun h w v same hi => OwnerWorkers.store h w v same hi) .netRx
      (OwnerReceive.wgReceive_checked msg src)
  intro w h hi
  obtain ⟨suffix,history,safe,_⟩ := owner w h hi.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases actual : (runPrefix (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) w h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨⟩,v⟩
    obtain ⟨prior,next,old,step,after⟩ := normal hi (Prod.ext actual rfl)
    exact ⟨prior,next,w,h,old,step,after⟩

/-- The original batch item uses this exact receive callback before its
inline poll; the multicast and TX cases remain the original observers. -/
theorem batchItem_source (d : Device) (cqes : List Int) (item : Leanux.Env.BatchItem) :
    RxHistory.batchItem d cqes item =
      batchItemWith AdmissionCaller.receive RxHistory.pollScheduledInline
        (fun family addr => RxHistory.audit (xmitMulticastLoopAudit family addr))
        (fun family addr packets mtu => RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu)))
        d cqes item := rfl

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionSection
