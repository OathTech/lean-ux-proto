import Leanux.Proofs.WG.Queues.ReceiveEffects
import Leanux.Proofs.WG.Queues.ConservationSource

/-! Conservation consequences of the existing traffic source paths. No new
transition interpreter is introduced. Each concrete theorem consumes its
original exact source certificate, including its actual nested receive calls. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TrafficEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- An algebraic conclusion, not source evidence or an account invariant.
All earlier carriers remain pending or occur in this exact fresh removal span. -/
def Conserved (cs next : Ledger) (h k : List RxHistory.Event) : Prop :=
  ∃ suffix,k=h++suffix ∧ ∀ c ∈ cs,c ∈ next ∨ c.packet ∈ NapiCarrier.removedPackets suffix

theorem refl : Conserved cs cs h h := ⟨[],by simp,fun _ member=>Or.inl member⟩

theorem trans (first : Conserved cs middle h j) (tail : Conserved middle next j k) :
    Conserved cs next h k := by
  obtain ⟨front,hfront,prior⟩ := first
  obtain ⟨back,hback,later⟩ := tail
  refine ⟨front++back,by rw [hback,hfront,List.append_assoc],?_⟩
  intro c member
  rcases prior c member with pending | removed
  · rcases later c pending with pending | removed
    · exact Or.inl pending
    · exact Or.inr (by simpa [NapiCarrier.removedPackets,List.filterMap_append] using
        (List.mem_append_right (NapiCarrier.removedPackets front) removed))
  · exact Or.inr (by simpa [NapiCarrier.removedPackets,List.filterMap_append] using
      (List.mem_append_left (NapiCarrier.removedPackets back) removed))

theorem removal (history : k=h++suffix) :
    Conserved cs (remaining cs (NapiCarrier.removedPackets suffix)) h k :=
  ⟨suffix,history,fun _ member=>ConservationAlgebra.pending_or_removed member⟩

theorem receive (step : AdmissionCaller.Step cs next msg src w v h k) : Conserved cs next h k := by
  obtain ⟨suffix,hist⟩ := AdmissionCaller.step_appends step
  exact ⟨suffix,hist,fun _ member=>Or.inl (ReceiveEffects.retains step.2 member)⟩

theorem netRx (step : AdmissionSection.Step cs next msg src w v h k) : Conserved cs next h k := by
  obtain ⟨u,t,_,body,_⟩ := step
  exact receive body

theorem floodSection (step : FloodSection.Step cs next msg src w v h k) : Conserved cs next h k := by
  obtain ⟨admitted,u,t,r,j,suffix,_,body,_,hist,rfl,_⟩ := step
  exact trans (receive body) (removal hist)

theorem floodStep (step : FloodLoop.Step family src msg cs next w v h k) : Conserved cs next h k := by
  obtain ⟨u,_,body⟩ := step
  exact floodSection body

theorem floodPath (path : FloodLoop.Path family src messages cs w h next v k) :
    Conserved cs next h k := by
  induction path with
  | nil => exact refl
  | cons step tail ih => exact trans (floodStep step) ih

/-- Both scheduling modes retain a residual carrier unless this exact call
records its removal; no empty-completion premise is used. -/
theorem flood (outcome : FloodAccount.Outcome cs next count port family messages w v h k result) :
    Conserved cs next h k := by
  obtain ⟨src,u,t,j,middle,suffix,_,path,_,hist,rfl⟩ := outcome
  exact trans (floodPath path) (removal hist)

theorem batchStep (step : BatchAccount.Step d cqes item out cs next w v h k) :
    Conserved cs next h k := by
  cases item with
  | inject family port msg =>
    obtain ⟨src,u,_,body,_⟩ := step
    exact floodSection body
  | xmit family addr payload opts =>
    obtain ⟨_,suffix,hist,rfl⟩ := step
    exact removal hist

theorem batchPath (path : BatchAccount.Path d entries cqes cs w h out next v k) :
    Conserved cs next h k := by
  induction path with
  | nil => exact refl
  | done step => exact batchStep step
  | yield step tail ih => exact trans (batchStep step) ih

theorem batch (outcome : BatchAccount.Outcome cs next entries w v h k result) :
    Conserved cs next h k := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,_,path,_,hist,rfl⟩ := outcome
  exact trans (batchPath path) (removal hist)

theorem inject (outcome : ConservationSource.InjectFinal cs family port msg tos ll dest w h result v k next) :
    Conserved cs next h k := by
  obtain ⟨src,u,t,j,admitted,suffix,_,step,_,hist,rfl⟩ := outcome
  exact trans (netRx step) (removal hist)

/-- Specify one actual accepted receive occurrence and a later conserved
source span. This retains its exact history cut even for equal-valued calls. -/
theorem accepted_fate (step : AdmissionCaller.Step cs next msg src w v h k)
    (accepted : ReceiveEffects.Accepted cs next msg src w.wg v.wg w.ambient v.ambient c)
    (tail : Conserved next final k l) :
    runPrefix (AdmissionCaller.receive msg src) w h=(.ok ((),v),k) ∧
      ∃ suffix,l=k++suffix ∧ (c ∈ final ∨ c.packet ∈ NapiCarrier.removedPackets suffix) := by
  obtain ⟨suffix,hist,kept⟩ := tail
  refine ⟨step.1,suffix,hist,kept c ?_⟩
  rw [ReceiveEffects.accepted_ledger accepted]
  exact List.mem_cons_self

end Leanux.Proofs.WG.Queues.RxCredits.TrafficEffects
