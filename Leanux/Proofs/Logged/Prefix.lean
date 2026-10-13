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

/-- A result-dependent contract retaining the event prefix on every failure.
The success postcondition can pass a resolved identity to the next operation. -/
def PrefixEnsures (P : List Event → World → Prop) (S : List Event → Prop)
    (g : PrefixM Event α) (Q : α → List Event → World → Prop) : Prop :=
  ∀ w h, P h w →
    ∃ suffix, (runPrefix g w h).2 = h ++ suffix ∧ S (runPrefix g w h).2 ∧
      match (runPrefix g w h).1 with
      | .error _ => True
      | .ok (x, w') => Q x (runPrefix g w h).2 w'

theorem PrefixEnsures.pure (hs : ∀ h w, P h w → S h)
    (hq : ∀ h w, P h w → Q x h w) : PrefixEnsures P S (pure x) Q := by
  intro w h hp
  exact ⟨[], by simp, hs h w hp, hq h w hp⟩

theorem PrefixEnsures.lift (a : M α) (hs : ∀ h w, P h w → S h)
    (hq : ∀ h w x v, P h w → a.run w = .ok (x, v) → Q x h v) :
    PrefixEnsures P S (liftPrefix a) Q := by
  intro w h hp
  refine ⟨[], by simp, hs h w hp, ?_⟩
  simp only [runPrefix_lift]
  cases hr : a.run w with
  | error _ => trivial
  | ok out => exact hq h w out.1 out.2 hp hr

theorem PrefixEnsures.consequence (hg : PrefixEnsures P S g Q)
    (hp : ∀ h w, P' h w → P h w)
    (hq : ∀ x h w, Q x h w → Q' x h w) : PrefixEnsures P' S g Q' := by
  intro w h hi
  obtain ⟨suffix, he, hs, ho⟩ := hg w h (hp h w hi)
  refine ⟨suffix, he, hs, ?_⟩
  cases hr : (runPrefix g w h).1 with
  | error _ => trivial
  | ok out => exact hq out.1 _ out.2 (by simpa only [hr] using ho)

theorem PrefixEnsures.bind (hg : PrefixEnsures P S g Q)
    (hf : ∀ x, PrefixEnsures (Q x) S (f x) R) : PrefixEnsures P S (g >>= f) R := by
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

/-- Branch composition retains the chosen branch's result-dependent contract. -/
theorem PrefixEnsures.ite (p : Prop) [Decidable p]
    (ht : p → PrefixEnsures P S gt Q) (he : ¬p → PrefixEnsures P S ge Q) :
    PrefixEnsures P S (if p then gt else ge) Q := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

/-- Every outcome has a safe appended event prefix. Only successful outcomes
also have a final World on which to require the state invariant. -/
def PrefixPreserves (I : List Event → World → Prop) (S : List Event → Prop)
    (g : PrefixM Event α) : Prop :=
  ∀ w h, I h w →
    ∃ suffix, (runPrefix g w h).2 = h ++ suffix ∧ S (runPrefix g w h).2 ∧
      match (runPrefix g w h).1 with
      | .error _ => True
      | .ok (_, w') => I (runPrefix g w h).2 w'

theorem PrefixEnsures.preserves (hg : PrefixEnsures I S g (fun _ => I)) :
    PrefixPreserves I S g := hg

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

/-- Conditional composition retains the chosen branch's failed prefix. -/
theorem PrefixPreserves.ite (p : Prop) [Decidable p]
    (ht : p → PrefixPreserves I S gt) (he : ¬p → PrefixPreserves I S ge) :
    PrefixPreserves I S (if p then gt else ge) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

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
