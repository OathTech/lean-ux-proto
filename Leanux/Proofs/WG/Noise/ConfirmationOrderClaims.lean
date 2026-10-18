import Leanux.Proofs.WG.Noise.ConfirmationOrderSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConfirmationOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation

theorem initialized_complete (trace : Runner.Trace) (placeholders : Bool) :
    ∃ qs,
      observations trace placeholders = .ok qs ∧
      confirmationIds trace placeholders = .ok (successful qs) ∧
      qs.Pairwise (fun a b => a.position < b.position) ∧
      qs.length = consumedCount (history trace placeholders) ∧
      (∀ q, q ∈ qs ↔ OccursAt trace placeholders q) ∧
      (∀ q ∈ qs,
        q.observation.Valid ∧ q.observation.Facts ∧
        projectedStampAt q.observation.entry q.observation.packet.keypair = some q.internalId ∧
        (q.observation.confirmed = true → q.observation.ConfirmedStamp q.internalId)) := by
  obtain ⟨qs,eq,ids,ordered⟩ := initialized_ordered trace placeholders
  refine ⟨qs,eq,ids,ordered.increasing,ordered.length,?_,?_⟩
  · intro q
    exact ⟨ordered.occurs q,ordered.complete_occurs q⟩
  · intro q member
    exact (occurs_facts (ordered.occurs q member)).2

theorem confirmationIds_sound (trace : Runner.Trace) (placeholders : Bool)
    (ids : List Nat) (run : confirmationIds trace placeholders = .ok ids)
    (allocation : Nat) (member : allocation ∈ ids) :
    ∃ q, OccursAt trace placeholders q ∧
      q.observation.confirmed = true ∧ q.internalId = allocation := by
  obtain ⟨qs,eq,idsEq,ordered⟩ := initialized_ordered trace placeholders
  have same := Except.ok.inj (run.symm.trans idsEq)
  subst ids
  obtain ⟨pre,post,n,id,stamp,r,q,position,member,matched,success,value⟩ :=
    ordered.success_sound allocation member
  exact ⟨q,ordered.occurs q member,success,value⟩

theorem confirmationIds_complete (trace : Runner.Trace) (placeholders : Bool)
    (q : Record) (occurs : OccursAt trace placeholders q)
    (confirmed : q.observation.confirmed = true) :
    ∃ left right, confirmationIds trace placeholders =
      .ok (left ++ q.internalId :: right) := by
  obtain ⟨qs,eq,idsEq,ordered⟩ := initialized_ordered trace placeholders
  obtain ⟨before,after,split⟩ := List.append_of_mem (ordered.complete_occurs q occurs)
  refine ⟨successful before,successful after,?_⟩
  rw [idsEq,split,successful_append]
  simp only [successful,List.filterMap_cons,confirmed,ite_true]

end Leanux.Proofs.WG.Noise.ConfirmationOrder
