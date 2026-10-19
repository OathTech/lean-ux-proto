import Leanux.Proofs.Logged.WGPrefix

/-! A finite native loop retains the exact processed packet sequence. Early
returns have their own postcondition; normal traversal keeps order and length. -/
namespace Leanux.Proofs.WG.TransmitSecurity
open Leanux Leanux.Proofs.Logged

theorem forIn_processed {E α β : Type} (xs seen : List α) (initial : β)
    (body : α → β → WGPrefix E (ForInStep β))
    (I : List α → β → List E → WGWorld → Ambient → Prop)
    (Done : β → List E → WGWorld → Ambient → Prop) (Safe : List E → Prop)
    (safeI : ∀ seen b h w a, I seen b h w a → Safe h)
    (safeDone : ∀ b h w a, Done b h w a → Safe h)
    (step : ∀ x seen b, StatePrefixEnsures (I seen b) Safe (body x b)
      (fun result => match result with
       | .done next => Done next
       | .yield next => I (seen ++ [x]) next)) :
    StatePrefixEnsures (I seen initial) Safe (forIn xs initial body)
      (fun result h w a => Done result h w a ∨ I (seen ++ xs) result h w a) := by
  induction xs generalizing seen initial with
  | nil =>
    apply StatePrefixEnsures.pure _ (safeI seen initial)
    intro h w a hi
    exact Or.inr (by simpa only [List.append_nil] using hi)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (step x seen initial)
    intro result
    cases result with
    | done next =>
      apply StatePrefixEnsures.pure _ (safeDone next)
      intro h w a hi
      exact Or.inl hi
    | yield next =>
      simpa only [List.append_assoc,List.singleton_append] using ih (seen ++ [x]) next

end Leanux.Proofs.WG.TransmitSecurity
