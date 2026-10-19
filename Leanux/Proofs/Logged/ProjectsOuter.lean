import Leanux.Proofs.Logged.PrefixOuter
import Leanux.Proofs.Logged.ProjectsPrefix

/-! Exact indexed-result and retained-history projections between outer
observers. The entry history and both failed histories stay unrestricted. -/
namespace Leanux.Proofs.Logged
open Leanux

def ProjectsOuter (ρ : E → Option F) (p : α → β)
    (g : PrefixOuter E α) (a : PrefixOuter F β) : Prop :=
  ∀ h, runPrefixOuter a (h.filterMap ρ) =
    ((runPrefixOuter g h).1.map p, (runPrefixOuter g h).2.filterMap ρ)

theorem projectsOuter_pure (ρ : E → Option F) (p : α → β) (x : α) :
    ProjectsOuter ρ p (pure x) (pure (p x)) := fun _ => rfl

theorem projectsOuter_pure_of (ρ : E → Option F) (p : α → β) {x : α} {y : β}
    (h : p x = y) : ProjectsOuter ρ p (pure x) (pure y) := by
  subst y
  exact projectsOuter_pure ρ p x

theorem projectsOuter_throw (ρ : E → Option F) (p : α → β) (e : Nat × Stop) :
    ProjectsOuter ρ p (throw e) (throw e) := fun _ => rfl

theorem projectsOuter_bind (ρ : E → Option F) (p : α → β) (q : γ → δ)
    (hg : ProjectsOuter ρ p g a) (hf : ∀ x, ProjectsOuter ρ q (f x) (b (p x))) :
    ProjectsOuter ρ q (g >>= f) (a >>= b) := by
  intro h
  rw [runPrefixOuter_bind, runPrefixOuter_bind, hg h]
  cases hr : runPrefixOuter g h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok x => exact hf x hist

theorem projectsOuter_ite (ρ : E → Option F) (p : Prop) [Decidable p] (f : α → β)
    (ht : p → ProjectsOuter ρ f gt ot) (he : ¬p → ProjectsOuter ρ f ge ae) :
    ProjectsOuter ρ f (if p then gt else ge) (if p then ot else ae) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem projectsOuter_forIn (ρ : E → Option F) (xs : List α) (init : β)
    (g : α → β → PrefixOuter E (ForInStep β))
    (a : α → β → PrefixOuter F (ForInStep β))
    (ha : ∀ x b, ProjectsOuter ρ id (g x b) (a x b)) :
    ProjectsOuter ρ id (forIn xs init g) (forIn xs init a) := by
  induction xs generalizing init with
  | nil => simpa only [List.forIn_nil, id_eq] using projectsOuter_pure ρ id init
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply projectsOuter_bind ρ id id (ha x init)
    intro step
    cases step with
    | done b => exact projectsOuter_pure ρ id b
    | yield b => exact ih b

theorem projectsOuter_array (ρ : E → Option F) (xs : Array α) (init : β)
    (g : α → β → PrefixOuter E (ForInStep β))
    (a : α → β → PrefixOuter F (ForInStep β))
    (ha : ∀ x b, ProjectsOuter ρ id (g x b) (a x b)) :
    ProjectsOuter ρ id (forIn xs init g) (forIn xs init a) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact projectsOuter_forIn ρ xs.toList init g a ha

theorem projectsOuter_runAt (ρ : E → Option F) (p : α → β)
    {g : PrefixT E State α} {a : PrefixT F State β}
    (hg : ProjectsPrefix ρ p g a) (index : Nat) (w : State) :
    ProjectsOuter ρ (fun (x,v) => (p x,v)) (runAtPrefix index w g) (runAtPrefix index w a) := by
  intro h
  simp only [runAtPrefix_run,hg w h]
  cases hr : (runPrefix g w h).1 <;> rfl

theorem projectsOuter_runAt_id (ρ : E → Option F)
    {g : PrefixT E State α} {a : PrefixT F State α}
    (hg : ProjectsPrefix ρ id g a) (index : Nat) (w : State) :
    ProjectsOuter ρ id (runAtPrefix index w g) (runAtPrefix index w a) :=
  projectsOuter_runAt ρ id hg index w

end Leanux.Proofs.Logged
