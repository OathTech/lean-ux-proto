import Leanux.Proofs.WG.Roaming.HandshakeInitializedBridge
import Leanux.Proofs.WG.Roaming.PollAuthenticationCheckSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.Proofs.Logged

theorem initialized_safe (trace : Runner.Trace) (placeholders : Bool) :
    RxValid (initializedHistory trace placeholders) := by
  have checked := HandshakeAttemptTransport.Initialized.safe receiver
    (by intro r member; cases member) trace placeholders
  simpa only [safe_transport,initializedHistory] using checked

theorem initialized_occurs_iff (trace : Runner.Trace) (placeholders : Bool) (q : Occurrence) :
    q ∈ initializedAttempts trace placeholders ↔ q.Occurs trace placeholders := by
  constructor
  · intro member
    obtain ⟨⟨event,index⟩,member,found⟩ := List.mem_filterMap.mp member
    have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp member
    cases event with
    | inl event => simp only [extractOccurrence,reduceCtorEq] at found
    | inr attempt =>
      simp only [extractOccurrence,Option.some.injEq] at found
      subst q
      obtain ⟨pre,post,split,length⟩ := PollAuthentication.getElem_split atIndex
      exact ⟨pre,post,split,length.symm⟩
  · rintro ⟨pre,post,split,position⟩
    apply List.mem_filterMap.mpr
    refine ⟨(.inr q.attempt,pre.length),?_,?_⟩
    · apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp only [split,List.getElem?_append_right (l₁ := pre) (Nat.le_refl pre.length),Nat.sub_self,
        List.getElem?_cons_zero]
    · simp only [extractOccurrence,← position]

theorem initialized_occurrence_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (q : Occurrence) (occurs : q.Occurs trace placeholders) : Authenticated q.attempt := by
  obtain ⟨pre,post,split,_⟩ := occurs
  apply initialized_safe trace placeholders q.attempt
  apply List.mem_filterMap.mpr
  exact ⟨.inr q.attempt,by rw [split]; simp,rfl⟩

theorem initialized_original (trace : Runner.Trace) (placeholders : Bool) :
    (initializedInspection trace placeholders).outcome = Runner.executeTrace trace placeholders :=
  HandshakeAttemptTransport.Initialized.outcome_original receiver trace placeholders

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
