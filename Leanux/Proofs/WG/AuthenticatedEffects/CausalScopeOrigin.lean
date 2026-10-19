import Leanux.Proofs.WG.AuthenticatedEffects.CausalScope

/-! A current lexical token must originate at an actual earlier entry in the
same history. Errors and missing contexts stay explicit; this lemma neither
manufactures an entry nor treats a token as an authorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

theorem fold_error (events : List (Event Cause)) (error : Malformed) :
    events.foldl advance (.error error) = .error error := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    change rest.foldl advance (.error error) = .error error
    exact ih

theorem fold_origin (events : List (Event Cause)) (before after : List (Token Cause))
    (token : Token Cause) (run : events.foldl advance (.ok before) = .ok after)
    (member : token ∈ after) : token ∈ before ∨ Event.entered token ∈ events := by
  induction events generalizing before with
  | nil =>
    cases run
    exact Or.inl member
  | cons event rest ih =>
    cases event with
    | entered fresh =>
      have origin := ih (fresh :: before) run
      rcases origin with initial | earlier
      · rcases List.mem_cons.mp initial with equal | old
        · exact Or.inr (by simp only [equal,List.mem_cons, true_or])
        · exact Or.inl old
      · exact Or.inr (List.mem_cons_of_mem _ earlier)
    | exited position =>
      cases before with
      | nil =>
        change rest.foldl advance (.error .unmatchedExit) = .ok after at run
        rw [fold_error] at run
        cases run
      | cons top tail =>
        by_cases same : top.position = position
        · have next : rest.foldl advance (.ok tail) = .ok after := by
            change rest.foldl advance (if top.position = position then .ok tail else .error .wrongExit) = .ok after at run
            simpa only [same,↓reduceIte] using run
          rcases ih tail next with initial | earlier
          · exact Or.inl (List.mem_cons_of_mem _ initial)
          · exact Or.inr (List.mem_cons_of_mem _ earlier)
        · have failed : rest.foldl advance (.error .wrongExit) = .ok after := by
            change rest.foldl advance (if top.position = position then .ok tail else .error .wrongExit) = .ok after at run
            simpa only [same,↓reduceIte] using run
          rw [fold_error] at failed
          cases failed

theorem current_origin (decode : E → Option (Event Cause)) (history : List E)
    (token : Token Cause) (currentToken : current decode history = .ok (some token)) :
    ∃ before event after, history = before ++ event :: after ∧ decode event = some (.entered token) := by
  have present : Event.entered token ∈ history.filterMap decode := by
    unfold current at currentToken
    cases result : stack (history.filterMap decode) with
    | error error => rw [result] at currentToken; cases currentToken
    | ok tokens =>
      rw [result] at currentToken
      cases tokens with
      | nil => cases currentToken
      | cons first tail =>
        have equal : first = token := by cases currentToken; rfl
        subst first
        have origin := fold_origin (history.filterMap decode) [] (token :: tail) token result (by simp)
        exact origin.resolve_left (by simp)
  obtain ⟨event,member,decoded⟩ := List.mem_filterMap.mp present
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp member
  exact ⟨before,event,after,position,decoded⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
