import Leanux.Proofs.Logged.Prefix
import Init.Data.Array.Lemmas

/-! Indexed runner errors with observation state outside the exception layer.
The World stays an explicit runner variable; a Stop retains the reached history. -/
namespace Leanux.Proofs.Logged
open Leanux Std.Do

abbrev PrefixOuter (Event : Type) := ExceptT (Nat × Stop) (StateM (List Event))

def runPrefixOuter (g : PrefixOuter Event α) (h : List Event) :
    Except (Nat × Stop) α × List Event := g.run.run h

def ErasesOuter (g : PrefixOuter Event α) (a : Except (Nat × Stop) α) : Prop :=
  ∀ h, (runPrefixOuter g h).1 = a

@[simp] theorem runPrefixOuter_pure (x : α) (h : List Event) :
    runPrefixOuter (pure x) h = (.ok x, h) := rfl

@[simp] theorem runPrefixOuter_throw (e : Nat × Stop) (h : List Event) :
    runPrefixOuter (throw e : PrefixOuter Event α) h = (.error e, h) := rfl

theorem runPrefixOuter_bind (g : PrefixOuter Event α) (f : α → PrefixOuter Event β)
    (h : List Event) :
    runPrefixOuter (g >>= f) h =
      match runPrefixOuter g h with
      | (.error e, h') => (.error e, h')
      | (.ok x, h') => runPrefixOuter (f x) h' := by
  unfold runPrefixOuter
  rw [ExceptT.run_bind, StateT.run_bind]
  cases hr : g.run.run h with
  | mk result hist => cases result <;> rfl

theorem erasesOuter_pure (x : α) :
    ErasesOuter (pure x : PrefixOuter Event α) (pure x) := fun _ => rfl

theorem erasesOuter_throw (e : Nat × Stop) :
    ErasesOuter (throw e : PrefixOuter Event α) (throw e) := fun _ => rfl

theorem erasesOuter_bind (hg : ErasesOuter g a)
    (hf : ∀ x, ErasesOuter (f x) (b x)) : ErasesOuter (g >>= f) (a >>= b) := by
  intro h
  rw [runPrefixOuter_bind]
  have he := hg h
  cases hr : runPrefixOuter g h with
  | mk result hist =>
    simp only [hr] at he
    cases result with
    | error e => rw [← he]; rfl
    | ok x => rw [← he]; exact hf x hist

theorem erasesOuter_map (f : α → β) (hg : ErasesOuter g a) :
    ErasesOuter (f <$> g) (f <$> a) := by
  simpa only [map_eq_pure_bind] using
    erasesOuter_bind hg (fun x => erasesOuter_pure (f x))

theorem erasesOuter_ite (p : Prop) [Decidable p]
    (ht : p → ErasesOuter gt ot) (he : ¬p → ErasesOuter ge oe) :
    ErasesOuter (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem erasesOuter_forIn (xs : List α) (b : β)
    (g : α → β → PrefixOuter Event (ForInStep β))
    (a : α → β → Except (Nat × Stop) (ForInStep β))
    (ha : ∀ x b, ErasesOuter (g x b) (a x b)) :
    ErasesOuter (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erasesOuter_pure b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erasesOuter_bind (ha x b)
    intro step
    cases step with
    | done b => exact erasesOuter_pure b
    | yield b => exact ih b

theorem erasesOuter_array (xs : Array α) (b : β)
    (g : α → β → PrefixOuter Event (ForInStep β))
    (a : α → β → Except (Nat × Stop) (ForInStep β))
    (ha : ∀ x b, ErasesOuter (g x b) (a x b)) :
    ErasesOuter (forIn xs b g) (forIn xs b a) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact erasesOuter_forIn _ b g a ha

/-- Attach the exact operation index without dropping a failed inner history. -/
def runAtPrefix (index : Nat) (w : World) (g : PrefixM Event α) :
    PrefixOuter Event (α × World) := ExceptT.mk fun h =>
  let (r, h') := runPrefix g w h
  (r.mapError (fun e => (index, e)), h')

@[simp] theorem runAtPrefix_run (index : Nat) (w : World) (g : PrefixM Event α)
    (h : List Event) :
    runPrefixOuter (runAtPrefix index w g) h =
      ((runPrefix g w h).1.mapError (fun e => (index, e)), (runPrefix g w h).2) := rfl

theorem runAtPrefix_erases (index : Nat) (w : World) (hg : ErasesPrefix g a) :
    ErasesOuter (runAtPrefix index w g) ((a.run w).mapError (fun e => (index, e))) := by
  intro h
  simp only [runAtPrefix_run, hg w h]

/-- Both postcondition branches receive the retained event state. In particular,
the exception postcondition is not the vacuous `mayThrow` postcondition. -/
theorem prefixOuter_wp_iff (g : PrefixOuter Event α) (P : List Event → Prop)
    (Q : α → List Event → Prop) (E : (Nat × Stop) → List Event → Prop) :
    (⦃fun h => ⌜P h⌝⦄ g ⦃post⟨fun x h => ⌜Q x h⌝, fun e h => ⌜E e h⌝⟩⦄) ↔
      ∀ h, P h → match runPrefixOuter g h with
        | (.ok x, h') => Q x h'
        | (.error e, h') => E e h' := by
  constructor
  all_goals intro hg h hp
  all_goals have hh := hg h hp
  all_goals cases hr : g h with
    | mk result hist =>
      cases result <;>
        simpa [runPrefixOuter, WP.wp, PredTrans.pushExcept, PredTrans.pushArg,
          PredTrans.apply, StateT.run, ExceptT.run, Id.run, PredTrans.pure,
          Pure.pure, hr] using hh

/-- An inner prefix contract becomes a runner contract with the same failed
history and its result-dependent successful World predicate. -/
theorem runAtPrefix_wp {g : PrefixM Event α} {P : List Event → World → Prop}
    {S : List Event → Prop} {Q : α → List Event → World → Prop}
    (hg : PrefixEnsures P S g Q) (index : Nat) (w : World) :
    ⦃fun h => ⌜P h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜Q out.1 h out.2⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  intro h hi
  obtain ⟨suffix, happend, hs, hq⟩ := hg w h hi
  rw [runAtPrefix_run]
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e => simpa only [hr, Except.mapError] using hs
    | ok out => simpa only [hr, Except.mapError] using hq

end Leanux.Proofs.Logged
