import Leanux.Proofs.Framing.WP

/-! Observation state outside the exception layer. A later failure preserves
all observations made by its successful prefix while erasure keeps the original
result, complete World on success, and exact Stop on failure. -/
namespace Leanux.Proofs.Logged
open Leanux

abbrev PrefixM (Event : Type) := StateT World (ExceptT Stop (StateM (List Event)))

def runPrefix (g : PrefixM Event α) (w : World) (h : List Event) :
    Except Stop (α × World) × List Event := ((g.run w).run).run h

def liftPrefix (a : M α) : PrefixM Event α :=
  fun w => ExceptT.mk fun h => (a.run w, h)

def emitPrefix (e : Event) : PrefixM Event Unit :=
  fun w => ExceptT.mk fun h => (.ok ((), w), h ++ [e])

def ErasesPrefix (g : PrefixM Event α) (a : M α) : Prop :=
  ∀ w h, (runPrefix g w h).1 = a.run w

@[simp] theorem prefix_except_map_ok (f : α → β) (x : α) :
    (f <$> (Except.ok x : Except Stop α)) = .ok (f x) := rfl

@[simp] theorem prefix_except_map_error (f : α → β) (e : Stop) :
    (f <$> (Except.error e : Except Stop α)) = .error e := rfl

@[simp] theorem runPrefix_pure (x : α) (w : World) (h : List Event) :
    runPrefix (pure x) w h = (.ok (x, w), h) := rfl

@[simp] theorem runPrefix_lift (a : M α) (w : World) (h : List Event) :
    runPrefix (liftPrefix a) w h = (a.run w, h) := rfl

@[simp] theorem runPrefix_emit (e : Event) (w : World) (h : List Event) :
    runPrefix (emitPrefix e) w h = (.ok ((), w), h ++ [e]) := rfl

@[simp] theorem runPrefix_throw (e : Stop) (w : World) (h : List Event) :
    runPrefix (throw e : PrefixM Event α) w h = (.error e, h) := rfl

theorem erasesPrefix_throw (e : Stop) :
    ErasesPrefix (throw e : PrefixM Event α) (throw e) := fun _ _ => rfl

theorem runPrefix_bind (g : PrefixM Event α) (f : α → PrefixM Event β)
    (w : World) (h : List Event) :
    runPrefix (g >>= f) w h =
      match runPrefix g w h with
      | (.error e, h') => (.error e, h')
      | (.ok (x, w'), h') => runPrefix (f x) w' h' := by
  simp only [runPrefix, StateT.run_bind, ExceptT.run_bind]
  cases hr : ((g.run w).run).run h with
  | mk result hist => cases result <;> rfl

theorem erasesPrefix_pure (x : α) : ErasesPrefix (pure x : PrefixM Event α) (pure x) :=
  fun _ _ => rfl

theorem erasesPrefix_lift (a : M α) : ErasesPrefix (liftPrefix a : PrefixM Event α) a :=
  fun _ _ => rfl

theorem erasesPrefix_emit (e : Event) : ErasesPrefix (emitPrefix e) (pure ()) :=
  fun _ _ => rfl

theorem erasesPrefix_bind (hg : ErasesPrefix g a)
    (hf : ∀ x, ErasesPrefix (f x) (b x)) : ErasesPrefix (g >>= f) (a >>= b) := by
  intro w h
  rw [runPrefix_bind]
  have he := hg w h
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e =>
      simp only [hr] at he
      simp [← he, StateT.run_bind]
    | ok out =>
      rcases out with ⟨x, v⟩
      simp only [hr] at he
      simpa [← he, StateT.run_bind] using hf x v hist

theorem erasesPrefix_ite (p : Prop) [Decidable p]
    (ht : p → ErasesPrefix gt ot) (he : ¬ p → ErasesPrefix ge oe) :
    ErasesPrefix (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem erasesPrefix_forIn (xs : List α) (b : β)
    (g : α → β → PrefixM Event (ForInStep β)) (a : α → β → M (ForInStep β))
    (ha : ∀ x b, ErasesPrefix (g x b) (a x b)) :
    ErasesPrefix (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erasesPrefix_pure b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erasesPrefix_bind (ha x b)
    intro step
    cases step with
    | done b => exact erasesPrefix_pure b
    | yield b => exact ih b

/-- Every outcome has a safe appended event prefix. Only successful outcomes
also have a final World on which to require the state invariant. -/
def PrefixPreserves (I : List Event → World → Prop) (S : List Event → Prop)
    (g : PrefixM Event α) : Prop :=
  ∀ w h, I h w →
    ∃ suffix, (runPrefix g w h).2 = h ++ suffix ∧ S (runPrefix g w h).2 ∧
      match (runPrefix g w h).1 with
      | .error _ => True
      | .ok (_, w') => I (runPrefix g w h).2 w'

theorem PrefixPreserves.pure (hs : ∀ h w, I h w → S h) (x : α) :
    PrefixPreserves I S (pure x) := by
  intro w h hi
  exact ⟨[], by simp, hs h w hi, hi⟩

theorem PrefixPreserves.bind (hg : PrefixPreserves I S g)
    (hf : ∀ x, PrefixPreserves I S (f x)) : PrefixPreserves I S (g >>= f) := by
  intro w h hi
  obtain ⟨s, he, hs, hout⟩ := hg w h hi
  cases hr : runPrefix g w h with
  | mk result hist =>
    simp only [hr] at he hs hout
    cases result with
    | error e =>
      simpa only [runPrefix_bind, hr] using (show ∃ suffix,
        hist = h ++ suffix ∧ S hist ∧ True from ⟨s, he, hs, True.intro⟩)
    | ok out =>
      rcases out with ⟨x, v⟩
      obtain ⟨t, ht, hsafe, hend⟩ := hf x v hist hout
      refine ⟨s ++ t, ?_, ?_, ?_⟩
      · rw [runPrefix_bind, hr]
        change (runPrefix (f x) v hist).2 = h ++ (s ++ t)
        rw [ht, he, List.append_assoc]
      · simpa only [runPrefix_bind, hr] using hsafe
      · simpa only [runPrefix_bind, hr] using hend

theorem PrefixPreserves.forIn (xs : List α) (b : β)
    (g : α → β → PrefixM Event (ForInStep β))
    (hs : ∀ h w, I h w → S h) (hg : ∀ x b, PrefixPreserves I S (g x b)) :
    PrefixPreserves I S (forIn xs b g) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using PrefixPreserves.pure hs b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixPreserves.bind (hg x b)
    intro step
    cases step with
    | done b => exact PrefixPreserves.pure hs b
    | yield b => exact ih b

end Leanux.Proofs.Logged
