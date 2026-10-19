import Leanux.Proofs.Logged.Projected

/-! Exact projection between two failure-retaining observers. Both the full
successful state and the Stop are retained, along with the projected log. -/
namespace Leanux.Proofs.Logged
open Leanux

variable {State : Type}

def ProjectsPrefix (ρ : E → Option F) (p : α → β)
    (g : PrefixT E State α) (t : PrefixT F State β) : Prop :=
  ∀ w h, runPrefix t w (h.filterMap ρ) =
    ((runPrefix g w h).1.map (fun (x, v) => (p x, v)), (runPrefix g w h).2.filterMap ρ)

theorem projectsPrefix_pure (ρ : E → Option F) (p : α → β) (x : α) :
    ProjectsPrefix (State := State) ρ p (pure x) (pure (p x)) := fun _ _ => rfl

theorem projectsPrefix_lift (ρ : E → Option F) (a : StateT State (Except Stop) α) :
    ProjectsPrefix ρ id (liftPrefix a) (liftPrefix a) := by
  intro w h
  simp only [runPrefix_lift]
  cases a.run w <;> rfl

theorem projectsPrefix_bind (ρ : E → Option F) (p : α → β) (q : γ → δ)
    (hg : ProjectsPrefix ρ p g a) (hf : ∀ x, ProjectsPrefix ρ q (f x) (b (p x))) :
    ProjectsPrefix ρ q (g >>= f) (a >>= b) := by
  intro w h
  rw [runPrefix_bind, runPrefix_bind, hg w h]
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨x, v⟩
      exact hf x v hist

theorem projectsPrefix_ite (ρ : E → Option F) (p : Prop) [Decidable p] (f : α → β)
    (ht : p → ProjectsPrefix ρ f gt ot) (he : ¬p → ProjectsPrefix ρ f ge oe) :
    ProjectsPrefix ρ f (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem projectsPrefix_emit (ρ : E → Option F) (e : E) :
    ProjectsPrefix (State := State) ρ id (emitPrefix e) ((ρ e).elim (pure ()) emitPrefix) := by
  intro w h
  cases he : ρ e <;> simp [he, List.filterMap_append, Except.map]

theorem projectsPrefix_forIn_map (ρ : E → Option F) (p : β → γ) (f : α → δ)
    (xs : List α) (b : β) (g : α → β → PrefixT E State (ForInStep β))
    (a : δ → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, ProjectsPrefix ρ (projectStep p) (g x b) (a (f x) (p b))) :
    ProjectsPrefix ρ p (forIn xs b g) (forIn (xs.map f) (p b) a) := by
  induction xs generalizing b with
  | nil => simpa only [List.map_nil, List.forIn_nil] using projectsPrefix_pure ρ p b
  | cons x xs ih =>
    rw [List.map_cons, List.forIn_cons, List.forIn_cons]
    apply projectsPrefix_bind ρ (projectStep p) p (ha x b)
    intro step
    cases step with
    | done b => exact projectsPrefix_pure ρ p b
    | yield b => exact ih b

theorem projectsPrefix_forIn (ρ : E → Option F) (p : β → γ)
    (xs : List α) (b : β) (g : α → β → PrefixT E State (ForInStep β))
    (a : α → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, ProjectsPrefix ρ (projectStep p) (g x b) (a x (p b))) :
    ProjectsPrefix ρ p (forIn xs b g) (forIn xs (p b) a) := by
  simpa only [List.map_id] using projectsPrefix_forIn_map ρ p id xs b g a ha

theorem projectsPrefix_range (ρ : E → Option F) (p : β → γ)
    (r : Std.Legacy.Range) (b : β) (g : Nat → β → PrefixT E State (ForInStep β))
    (a : Nat → γ → PrefixT F State (ForInStep γ))
    (ha : ∀ x b, ProjectsPrefix ρ (projectStep p) (g x b) (a x (p b))) :
    ProjectsPrefix ρ p (forIn r b g) (forIn r (p b) a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact projectsPrefix_forIn ρ p _ b g a ha

end Leanux.Proofs.Logged
