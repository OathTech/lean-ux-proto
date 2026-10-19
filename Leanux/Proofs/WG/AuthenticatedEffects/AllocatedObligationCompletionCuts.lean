import Leanux.Proofs.Logged.Prefix

/-! Result-aware contracts for a completion caller. Unlike a normal-endpoint
contract, an error must establish the caller's explicit stopped-frontier
predicate. Sequential composition never replaces that obligation with True. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionCuts
open Leanux Leanux.Proofs.Logged

def Ensures (P : List E → World → Prop) (stopped : Stop → List E → Prop)
    (action : PrefixM E α) (Q : α → List E → World → Prop) : Prop :=
  ∀ w history, P history w →
    ∃ suffix, (runPrefix action w history).2 = history ++ suffix ∧
      match (runPrefix action w history).1 with
      | .error reason => stopped reason (runPrefix action w history).2
      | .ok (value,after) => Q value (runPrefix action w history).2 after

theorem Ensures.pure (post : ∀ h w, P h w → Q value h w) :
    Ensures P stopped (pure value) Q := by
  intro w h before
  exact ⟨[],by simp,post h w before⟩

theorem Ensures.bind (first : Ensures P stopped action Q)
    (next : ∀ value, Ensures (Q value) stopped (continuation value) R) :
    Ensures P stopped (action >>= continuation) R := by
  intro w h before
  obtain ⟨added,grown,checked⟩ := first w h before
  cases run : runPrefix action w h with
  | mk result history =>
    simp only [run] at grown checked
    cases result with
    | error reason =>
      exact ⟨added,by simpa only [runPrefix_bind,run] using grown,
        by simpa only [runPrefix_bind,run] using checked⟩
    | ok result =>
      obtain ⟨value,v⟩ := result
      obtain ⟨suffix,extended,finished⟩ := next value v history checked
      refine ⟨added ++ suffix,?_,?_⟩
      · rw [runPrefix_bind,run]
        simpa only [grown,List.append_assoc] using extended
      · simpa only [runPrefix_bind,run] using finished

theorem Ensures.consequence (checked : Ensures P stopped action Q)
    (pre : ∀ h w, P' h w → P h w) (post : ∀ value h w, Q value h w → Q' value h w) :
    Ensures P' stopped action Q' := by
  intro w h before
  obtain ⟨suffix,grown,result⟩ := checked w h (pre h w before)
  refine ⟨suffix,grown,?_⟩
  cases outcome : (runPrefix action w h).1 with
  | error reason => simpa only [outcome] using result
  | ok out => exact post out.1 _ out.2 (by simpa only [outcome] using result)

theorem Ensures.choice (p : Prop) [Decidable p]
    (yes : p → Ensures P stopped first Q) (no : ¬p → Ensures P stopped second Q) :
    Ensures P stopped (if p then first else second) Q := by
  split
  · exact yes ‹p›
  · exact no ‹¬p›

/-- An actual failed run exports the supplied frontier certificate. There is
no successful-state or history-only fallback at this extraction boundary. -/
theorem Ensures.failed (checked : Ensures P stopped action Q) (before : P history w)
    (run : runPrefix action w history = (.error reason,after)) : stopped reason after := by
  obtain ⟨_,_,result⟩ := checked w history before
  simpa only [run] using result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionCuts
