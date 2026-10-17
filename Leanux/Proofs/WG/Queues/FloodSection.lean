import Leanux.Proofs.WG.Queues.AdmissionSection
import Leanux.Proofs.WG.Queues.HolderAfterBatch

/-! The actual flood/batch NET_RX body receives once, polls inline, then closes
its section. The ledger transition follows these exact admission/removal cuts. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.FloodSection
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def action (msg : List UInt8) (src : SkbSource) : RxHistory.Obs Unit := runWorkerPrefix .netRx do
  AdmissionCaller.receive msg src
  RxHistory.pollScheduledInline

theorem source_factor (msg src) : action msg src = (do
    AdmissionSection.enter
    AdmissionCaller.receive msg src
    RxHistory.pollScheduledInline
    AdmissionSection.leave) := by
  simp only [action,runWorkerPrefix,AdmissionSection.enter,AdmissionSection.leave,bind_assoc]
  rfl

/-- Ordered source witnesses only. The incoming history may contain arbitrary
older events, and repeated equal packets remain separate loop occurrences. -/
def Step (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : World) (h k : List RxHistory.Event) : Prop :=
  ∃ admitted u t r j suffix,
    runPrefix AdmissionSection.enter w h=(.ok ((),u),h) ∧
    AdmissionCaller.Step cs admitted msg src u t h j ∧
    runPrefix RxHistory.pollScheduledInline t j=(.ok ((),r),k) ∧
    k=j++suffix ∧ next=remaining admitted (NapiCarrier.removedPackets suffix) ∧
    runPrefix AdmissionSection.leave r k=(.ok ((),v),k)

theorem Step.source (step : Step cs next msg src w v h k) :
    runPrefix (action msg src) w h=(.ok ((),v),k) := by
  obtain ⟨admitted,u,t,r,j,suffix,start,receive,poll,_,_,stop⟩ := step
  rw [source_factor]
  simp only [runPrefix_bind,start,receive.1,poll,stop]

theorem Step.appends (step : Step cs next msg src w v h k) : ∃ suffix,k=h++suffix := by
  obtain ⟨admitted,u,t,r,j,suffix,_,receive,_,history,_,_⟩ := step
  obtain ⟨prior,old⟩ := AdmissionCaller.step_appends receive
  exact ⟨prior++suffix,by rw [history,old,List.append_assoc]⟩

theorem Step.unique (left : Step cs next msg src w v h k)
    (right : Step cs other msg src w v h k) : next=other := by
  obtain ⟨admitted,u,t,r,j,suffix,start,receive,poll,history,rfl,stop⟩ := left
  obtain ⟨admitted',u',t',r',j',suffix',start',receive',poll',history',rfl,stop'⟩ := right
  rw [start] at start'
  obtain ⟨⟨_,rfl⟩,_⟩ := start'
  have same := receive.1.symm.trans receive'.1
  obtain ⟨⟨_,rfl⟩,rfl⟩ := same
  have ledger := AdmissionCaller.step_unique receive receive'
  have suffixEq := List.append_cancel_left (history.symm.trans history')
  rw [ledger,suffixEq]

/-- A successful actual section constructs its transition and derives the
new account; neither a selected ledger nor output funding is assumed. -/
theorem normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (action msg src) w h=(.ok ((),v),k)) :
    ∃ next,Step cs next msg src w v h k ∧ HolderAuxiliary.Inv next loans k k v := by
  rw [source_factor] at run
  obtain ⟨x,u,j,start,rest⟩ := DecryptIteration.bind_normal run
  cases x
  have same : j=h := by simpa only [start] using AdmissionSection.enter_history w h
  subst j
  have entry := (AdmissionSection.enter_preserves w h hi).choose_spec.2.2
  rw [start] at entry
  obtain ⟨x,t,j,receive,rest⟩ := DecryptIteration.bind_normal rest
  cases x
  obtain ⟨prior,admitted,priorEq,receipt,afterReceive⟩ := AdmissionAuxiliary.receive_rebase entry receive
  have priorNil : prior=[] := by
    have len := congrArg List.length priorEq
    simp only [List.length_append] at len
    cases prior with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at len; omega
  have initial : remaining cs (NapiCarrier.removedPackets prior)=cs := by
    subst prior
    exact List.filter_eq_self.mpr (fun _ _=>rfl)
  rw [initial] at receipt
  obtain ⟨x,r,l,poll,stop⟩ := DecryptIteration.bind_normal rest
  cases x
  have same : k=l := by simpa only [stop] using AdmissionSection.leave_history r l
  subst l
  have afterPoll := (HolderAfterBatch.inlinePoll admitted loans j t j afterReceive).choose_spec.2.2
  rw [poll] at afterPoll
  obtain ⟨suffix,history,rebase⟩ := HolderInitial.rebase afterPoll
  have post := (AdmissionSection.leave_preserves r k rebase).choose_spec.2.2
  rw [stop] at post
  exact ⟨_,⟨admitted,u,t,r,j,suffix,start,receipt,poll,history,rfl,stop⟩,post⟩

theorem preserves (cs : Ledger) (loans : Reservations) (msg src) :
    PrefixEnsures (fun h w=>HolderAuxiliary.Inv cs loans h h w) OwnerChecks.Safe (action msg src)
      (fun _ k v=>∃ w h next,Step cs next msg src w v h k ∧ HolderAuxiliary.Inv next loans k k v) := by
  have owner : OwnerChecks.Preserves (action msg src) :=
    runWorkerPrefix_preserves (fun _ _ hi=>hi.safe) OwnerWorkers.store .netRx
      (PrefixPreserves.bind (OwnerReceive.wgReceive_checked msg src) (fun _=>OwnerWorkers.pollScheduledInline))
  intro w h hi
  obtain ⟨suffix,hist,safe,_⟩ := owner w h hi.2.1
  refine ⟨suffix,hist,safe,?_⟩
  cases actual : (runPrefix (action msg src) w h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨⟩,v⟩
    obtain ⟨next,step,post⟩ := normal hi (Prod.ext actual rfl)
    exact ⟨w,h,next,step,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.FloodSection
