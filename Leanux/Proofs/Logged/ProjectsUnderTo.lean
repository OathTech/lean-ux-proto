import Leanux.Proofs.Logged.ProjectsUnder

/-! Invariant-conditioned exact observer projection with a result map.
The complete state, Stop and reached history are retained. -/
namespace Leanux.Proofs.Logged
open Leanux

variable {State : Type}

def ProjectsUnderTo (I : List F → State → Prop) (ρ : E → Option F)
    (p : α → β) (g : PrefixT E State α) (a : PrefixT F State β) : Prop :=
  ∀ w h, I (h.filterMap ρ) w →
    runPrefix a w (h.filterMap ρ) =
      ((runPrefix g w h).1.map (fun (x, v) => (p x, v)),
        (runPrefix g w h).2.filterMap ρ)

theorem ProjectsPrefix.underTo (hg : ProjectsPrefix ρ p g a) :
    ProjectsUnderTo I ρ p g a := fun w h _ => hg w h

theorem ProjectsUnder.to_mapped (hg : ProjectsUnder I ρ g a) :
    ProjectsUnderTo I ρ id g a := by
  intro w h hi
  rw [hg w h hi]
  cases (runPrefix g w h).1 <;> rfl

theorem ProjectsUnderTo.identity (hg : ProjectsUnderTo I ρ id g a) :
    ProjectsUnder I ρ g a := by
  intro w h hi
  have he := hg w h hi
  cases hr : (runPrefix g w h).1 <;> simpa only [hr, Except.map, id] using he

theorem ProjectsUnderTo.preserves {E F α β : Type}
    {I : List F → State → Prop} {S : List F → Prop} {ρ : E → Option F}
    {p : α → β} {g : PrefixT E State α} {a : PrefixT F State β} (hg : ProjectsUnderTo I ρ p g a)
    (ha : PrefixPreserves I S a) :
    ∀ w h, I (h.filterMap ρ) w → S ((runPrefix g w h).2.filterMap ρ) ∧
      match (runPrefix g w h).1 with
      | .error _ => True
      | .ok (_, v) => I ((runPrefix g w h).2.filterMap ρ) v := by
  intro w h hi
  obtain ⟨_, _, hs, hp⟩ := ha w (h.filterMap ρ) hi
  rw [hg w h hi] at hs hp
  refine ⟨hs, ?_⟩
  cases hr : (runPrefix g w h).1 <;> simp only [hr, Except.map] at hp ⊢ <;> exact hp

theorem projectsUnderTo_pure (ρ : E → Option F) (p : α → β) (x : α) :
    ProjectsUnderTo I ρ p (pure x) (pure (p x)) := (projectsPrefix_pure ρ p x).underTo

theorem projectsUnderTo_lift (ρ : E → Option F) (a : StateT State (Except Stop) α) :
    ProjectsUnderTo I ρ id (liftPrefix a) (liftPrefix a) :=
  (projectsPrefix_lift ρ a).underTo

theorem projectsUnderTo_bind (ρ : E → Option F) (p : α → β) (q : γ → δ)
    (hg : ProjectsUnderTo I ρ p g a) (ha : PrefixPreserves I S a)
    (hf : ∀ x, ProjectsUnderTo I ρ q (f x) (b (p x))) :
    ProjectsUnderTo I ρ q (g >>= f) (a >>= b) := by
  intro w h hi
  have he := hg w h hi
  obtain ⟨_, _, _, hp⟩ := ha w (h.filterMap ρ) hi
  rw [he] at hp
  rw [runPrefix_bind, runPrefix_bind, he]
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨x, v⟩
      exact hf x v hist (by simpa only [hr, Except.map] using hp)

theorem projectsUnderTo_ite (ρ : E → Option F) (c : Prop) [Decidable c] (p : α → β)
    (ht : c → ProjectsUnderTo I ρ p gt ot)
    (he : ¬c → ProjectsUnderTo I ρ p ge oe) :
    ProjectsUnderTo I ρ p (if c then gt else ge) (if c then ot else oe) := by
  by_cases hc : c <;> simp only [hc, ↓reduceIte]
  · exact ht hc
  · exact he hc

theorem projectsUnderTo_forIn_map (ρ : E → Option F) (p : β → γ) (f : α → δ)
    (xs : List α) (b : β) (g : α → β → PrefixT E State (ForInStep β))
    (a : δ → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, PrefixPreserves I S (a x b))
    (hg : ∀ x b, ProjectsUnderTo I ρ (projectStep p) (g x b) (a (f x) (p b))) :
    ProjectsUnderTo I ρ p (forIn xs b g) (forIn (xs.map f) (p b) a) := by
  induction xs generalizing b with
  | nil => simpa only [List.map_nil, List.forIn_nil] using projectsUnderTo_pure ρ p b
  | cons x xs ih =>
    rw [List.map_cons, List.forIn_cons, List.forIn_cons]
    apply projectsUnderTo_bind ρ (projectStep p) p (hg x b) (ha _ _)
    intro step
    cases step with
    | done b => exact projectsUnderTo_pure ρ p b
    | yield b => exact ih b

theorem projectsUnderTo_forIn (ρ : E → Option F) (p : β → γ)
    (xs : List α) (b : β) (g : α → β → PrefixT E State (ForInStep β))
    (a : α → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, PrefixPreserves I S (a x b))
    (hg : ∀ x b, ProjectsUnderTo I ρ (projectStep p) (g x b) (a x (p b))) :
    ProjectsUnderTo I ρ p (forIn xs b g) (forIn xs (p b) a) := by
  simpa only [List.map_id] using projectsUnderTo_forIn_map ρ p id xs b g a ha hg

theorem projectsUnderTo_range (ρ : E → Option F) (p : β → γ)
    (r : Std.Legacy.Range) (b : β) (g : Nat → β → PrefixT E State (ForInStep β))
    (a : Nat → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, PrefixPreserves I S (a x b))
    (hg : ∀ x b, ProjectsUnderTo I ρ (projectStep p) (g x b) (a x (p b))) :
    ProjectsUnderTo I ρ p (forIn r b g) (forIn r (p b) a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact projectsUnderTo_forIn ρ p _ b g a ha hg

end Leanux.Proofs.Logged
