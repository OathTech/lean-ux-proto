import Leanux.Proofs.WG.Queues.ConservationAlgebra
import Leanux.Proofs.WG.Queues.AdmissionCaller

/-! Unwrap the actual receive front and its selected data admission. These
are source receipts, not funding fields or a new executable observer. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ReceiveEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- One actual accepted enqueue inside this native receive call. Both the
front and admission endpoints belong to this specified source occurrence. -/
def Accepted (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) (c : Carrier) : Prop :=
  ∃ ds u clock receipt ctx added ret middle time,
    ((AdmissionReceive.front msg src).run w).run a=.ok ((some ds,u),clock) ∧
    AdmissionOutcome.Outcome cs next msg src ds u v clock b receipt ∧
    receipt.value=some ctx ∧ AdmissionOutcome.carrier receipt.after ctx=some added ∧
    ((enqueuePerDeviceAndPeerRx ctx.slot).run receipt.after).run receipt.ambientAfter=
      .ok ((ret,middle),time) ∧ ret ≠ -ENOSPC ∧ c=enqueued added

theorem accepted_outcome (accepted : Accepted cs next msg src w v a b c) :
    AdmissionReceive.Outcome cs next msg src w v a b := by
  obtain ⟨ds,u,clock,receipt,ctx,added,ret,middle,time,front,outcome,_⟩ := accepted
  exact ⟨some ds,u,clock,front,receipt,outcome⟩

theorem accepted_ledger (accepted : Accepted cs next msg src w v a b c) : next=c::cs := by
  obtain ⟨ds,u,clock,receipt,ctx,added,ret,middle,time,front,outcome,value,selected,enqueue,ok,rfl⟩ := accepted
  exact ConservationAlgebra.admitted_ledger outcome value selected enqueue ok

theorem retains (outcome : AdmissionReceive.Outcome cs next msg src w v a b)
    (member : c ∈ cs) : c ∈ next := by
  obtain ⟨choice,u,clock,front,rest⟩ := outcome
  cases choice with
  | none => exact rest.1 ▸ member
  | some ds =>
    obtain ⟨receipt,outcome⟩ := rest
    exact ConservationAlgebra.admission_retains outcome member

/-- A new ledger entry identifies a real accepted admission in this exact
receive call; malformed headers and handshake queueing introduce none. -/
theorem origin (outcome : AdmissionReceive.Outcome cs next msg src w v a b)
    (member : c ∈ next) : c ∈ cs ∨ Accepted cs next msg src w v a b c := by
  obtain ⟨choice,u,clock,front,rest⟩ := outcome
  cases choice with
  | none => exact Or.inl (by simpa only [rest.1] using member)
  | some ds =>
    obtain ⟨receipt,outcome⟩ := rest
    have rest := outcome.2.2.2
    cases value:receipt.value with
    | none =>
      simp only [value] at rest
      exact Or.inl (by simpa only [rest.2.2] using member)
    | some ctx =>
      simp only [value] at rest
      obtain ⟨added,ret,middle,time,selected,enqueue,finish,choices,ledger⟩ := rest
      by_cases full : ret = -ENOSPC
      · simp only [full,ite_true] at ledger
        exact Or.inl (by simpa only [ledger] using member)
      · simp only [full,ite_false] at ledger
        rw [ledger] at member
        rcases List.mem_cons.mp member with same | old
        · exact Or.inr ⟨ds,u,clock,receipt,ctx,added,ret,middle,time,
            front,outcome,value,selected,enqueue,full,same⟩
        · exact Or.inl old

theorem caller_origin (step : AdmissionCaller.Step cs next msg src w v h k)
    (member : c ∈ next) : c ∈ cs ∨
      Accepted cs next msg src w.wg v.wg w.ambient v.ambient c :=
  origin step.2 member

/-- Distinct source receipts for this same receive endpoint cannot choose
different inserted carriers. This does not identify different call positions. -/
theorem accepted_unique (left : Accepted cs xs msg src w v a b c)
    (right : Accepted cs ys msg src w v a b d) : c=d := by
  have same := AdmissionReceive.Outcome.unique (accepted_outcome left) (accepted_outcome right)
  rw [accepted_ledger left,accepted_ledger right] at same
  exact (List.cons.inj same).1

/-- A normal call that never completed a data admission: either the receive
front selected no data continuation, or the actual admission front returned
none. This includes malformed-header rejection and handshake queueing. -/
def NoAdmission (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) : Prop :=
  ∃ choice u clock, ((AdmissionReceive.front msg src).run w).run a=.ok ((choice,u),clock) ∧
    match choice with
    | none => next=cs ∧ v=u ∧ b=clock
    | some ds => ∃ receipt,AdmissionOutcome.Outcome cs next msg src ds u v clock b receipt ∧
        receipt.value=none

/-- An admitted packet can instead hit the full peer receive queue (-ENOSPC). Its
original finishAfter run is retained, and the source selects the old ledger.
This is a normal-run receipt, not a totality assertion for that cleanup. -/
def PeerQueueFull (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) (c : Carrier) : Prop :=
  ∃ ds u clock receipt ctx middle time,
    ((AdmissionReceive.front msg src).run w).run a=.ok ((some ds,u),clock) ∧
    AdmissionOutcome.Outcome cs next msg src ds u v clock b receipt ∧
    receipt.value=some ctx ∧ AdmissionOutcome.carrier receipt.after ctx=some c ∧
    ((enqueuePerDeviceAndPeerRx ctx.slot).run receipt.after).run receipt.ambientAfter=
      .ok ((-ENOSPC,middle),time) ∧
    ((finishAfter ctx (-ENOSPC)).run middle).run time=.ok (((),v),b) ∧ next=cs

/-- Every normal original receive has one of these concrete source cuts.
Peer-queue-full cleanup is separate from accepted enqueue. Decrypt-ring full
(-EPIPE) remains accepted into the peer queue for DEAD/NAPI disposal. -/
theorem disposition (outcome : AdmissionReceive.Outcome cs next msg src w v a b) :
    NoAdmission cs next msg src w v a b ∨
      (∃ c,PeerQueueFull cs next msg src w v a b c) ∨
      ∃ c,Accepted cs next msg src w v a b c := by
  obtain ⟨choice,u,clock,front,rest⟩ := outcome
  cases choice with
  | none => exact Or.inl ⟨none,u,clock,front,rest⟩
  | some ds =>
    obtain ⟨receipt,outcome⟩ := rest
    have rest := outcome.2.2.2
    cases value:receipt.value with
    | none => exact Or.inl ⟨some ds,u,clock,front,receipt,outcome,value⟩
    | some ctx =>
      simp only [value] at rest
      obtain ⟨c,ret,middle,time,selected,enqueue,finish,choices,ledger⟩ := rest
      by_cases full : ret = -ENOSPC
      · subst ret
        exact Or.inr (Or.inl ⟨c,ds,u,clock,receipt,ctx,middle,time,front,outcome,value,
          selected,enqueue,finish,by simpa only [ite_true] using ledger⟩)
      · exact Or.inr (Or.inr ⟨enqueued c,ds,u,clock,receipt,ctx,c,ret,middle,time,
          front,outcome,value,selected,enqueue,full,rfl⟩)

end Leanux.Proofs.WG.Queues.RxCredits.ReceiveEffects
