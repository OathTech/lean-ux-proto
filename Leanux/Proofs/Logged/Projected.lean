import Leanux.Proofs.Logged.PrefixLoops

/-! Failure-retaining observers may carry extra information in a loop's local
accumulator. Erasure projects that accumulator while retaining the full World
and exact original Stop. -/
namespace Leanux.Proofs.Logged
open Leanux

def ErasesTo (p : α → β) (g : PrefixM Event α) (a : M β) : Prop :=
  ∀ w h, ((runPrefix g w h).1.map fun (x, v) => (p x, v)) = a.run w

theorem ErasesPrefix.to_projected (hg : ErasesPrefix g a) : ErasesTo id g a := by
  intro w h
  rw [hg w h]
  cases a.run w <;> rfl

theorem ErasesTo.identity (hg : ErasesTo id g a) : ErasesPrefix g a := by
  intro w h
  have he := hg w h
  cases hr : (runPrefix g w h).1 <;> simpa [hr, Except.map] using he

theorem erasesTo_pure (p : α → β) (x : α) :
    ErasesTo p (pure x : PrefixM Event α) (pure (p x)) := fun _ _ => rfl

theorem erasesTo_bind (p : α → β) (q : γ → δ)
    (hg : ErasesTo p g a) (hf : ∀ x, ErasesTo q (f x) (b (p x))) :
    ErasesTo q (g >>= f) (a >>= b) := by
  intro w h
  rw [runPrefix_bind]
  have he := hg w h
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e =>
      simp only [hr] at he
      simp [← he, StateT.run_bind, Except.map]
    | ok out =>
      rcases out with ⟨x, v⟩
      simp only [hr] at he
      simpa [← he, StateT.run_bind, Except.map] using hf x v hist

theorem erasesTo_ite (p : Prop) [Decidable p] (f : α → β)
    (ht : p → ErasesTo f gt ot) (he : ¬p → ErasesTo f ge oe) :
    ErasesTo f (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

def projectStep (p : α → β) : ForInStep α → ForInStep β
  | .done x => .done (p x)
  | .yield x => .yield (p x)

theorem erasesTo_forIn (p : β → γ) (xs : List α) (b : β)
    (g : α → β → PrefixM Event (ForInStep β)) (a : α → γ → M (ForInStep γ))
    (ha : ∀ x b, ErasesTo (projectStep p) (g x b) (a x (p b))) :
    ErasesTo p (forIn xs b g) (forIn xs (p b) a) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erasesTo_pure p b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erasesTo_bind (projectStep p) p (ha x b)
    intro step
    cases step with
    | done b => exact erasesTo_pure p b
    | yield b => exact ih b

theorem erasesTo_range (p : β → γ) (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixM Event (ForInStep β)) (a : Nat → γ → M (ForInStep γ))
    (ha : ∀ x b, ErasesTo (projectStep p) (g x b) (a x (p b))) :
    ErasesTo p (forIn r b g) (forIn r (p b) a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erasesTo_forIn p _ b g a ha

end Leanux.Proofs.Logged
