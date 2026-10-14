import Leanux.Proofs.Logged.ProjectsPrefix
import Leanux.Proofs.Logged.Focus

/-! Exact projection under an explicit entry invariant. Focusing an existing
observer needs only its appended-suffix contract, not a second source copy.
The equality includes the entire result, successful World, Stop and history. -/
namespace Leanux.Proofs.Logged
open Leanux

def ProjectsUnder (I : List F → World → Prop) (ρ : E → Option F)
    (g : PrefixM E α) (a : PrefixM F α) : Prop :=
  ∀ w h, I (h.filterMap ρ) w →
    runPrefix a w (h.filterMap ρ) =
      ((runPrefix g w h).1, (runPrefix g w h).2.filterMap ρ)

variable {E F G α β : Type} {I : List F → World → Prop} {S : List F → Prop}
  {ρ : E → Option F} {g : PrefixM E α} {a : PrefixM F α}

theorem ProjectsPrefix.under (hg : ProjectsPrefix ρ id g a) : ProjectsUnder I ρ g a := by
  intro w h _
  cases hr : (runPrefix g w h).1 <;> simpa [hr, Except.map] using hg w h

theorem projectsUnder_pure (ρ : E → Option F) (x : α) :
    ProjectsUnder I ρ (pure x) (pure x) := by intro w h _; rfl

theorem projectsUnder_lift (ρ : E → Option F) (a : M α) :
    ProjectsUnder I ρ (liftPrefix a) (liftPrefix a) := by intro w h _; rfl

theorem projectsUnder_emit (ρ : E → Option F) (e : E) (he : ρ e = none) :
    ProjectsUnder I ρ (emitPrefix e) (pure ()) := by
  intro w h _
  simp [List.filterMap_append, he]

theorem projectsUnder_bind (hg : ProjectsUnder I ρ g a)
    (ha : PrefixPreserves I S a) (hf : ∀ x, ProjectsUnder I ρ (f x) (b x)) :
    ProjectsUnder I ρ (g >>= f) (a >>= b) := by
  intro w h hi
  have he := hg w h hi
  obtain ⟨s, _, _, hp⟩ := ha w (h.filterMap ρ) hi
  rw [he] at hp
  rw [runPrefix_bind, runPrefix_bind, he]
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨x, v⟩
      exact hf x v hist (by simpa only [hr] using hp)

/-- A finite loop projects exactly while its lower body transports the entry invariant. -/
theorem projectsUnder_forIn (xs : List γ) (b : β)
    (g : γ → β → PrefixM E (ForInStep β)) (a : γ → β → PrefixM F (ForInStep β))
    (ha : ∀ x b, PrefixPreserves I S (a x b))
    (hg : ∀ x b, ProjectsUnder I ρ (g x b) (a x b)) :
    ProjectsUnder I ρ (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => exact projectsUnder_pure ρ b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply projectsUnder_bind (hg x b) (ha x b)
    intro step
    cases step with
    | done b => exact projectsUnder_pure ρ b
    | yield b => exact ih b

/-- Range-loop projection retains both normal loop exits and failed prefixes. -/
theorem projectsUnder_range (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixM E (ForInStep β)) (a : Nat → β → PrefixM F (ForInStep β))
    (ha : ∀ x b, PrefixPreserves I S (a x b))
    (hg : ∀ x b, ProjectsUnder I ρ (g x b) (a x b)) :
    ProjectsUnder I ρ (forIn r b g) (forIn r b a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact projectsUnder_forIn _ b g a ha hg

theorem projectsUnder_focus (encode : F → E) (ρ : E → Option F)
    (hd : ∀ e, ρ (encode e) = some e)
    (hg : ∀ w h, I h w → ∃ suffix, (runPrefix a w h).2 = h ++ suffix) :
    ProjectsUnder I ρ (focusPrefix encode ρ a) a := by
  intro w h hi
  obtain ⟨suffix, hs⟩ := hg w (h.filterMap ρ) hi
  have hr : runPrefix a w (h.filterMap ρ) =
      ((runPrefix a w (h.filterMap ρ)).1, h.filterMap ρ ++ suffix) := Prod.ext rfl hs
  rw [focusPrefix_suffix encode ρ a w h _ suffix hr]
  apply Prod.ext
  · rfl
  · simp [hs, List.filterMap_append, filterMap_encoded encode ρ hd]

theorem PrefixPreserves.projects_focus (ha : PrefixPreserves I S a)
    (encode : F → E) (ρ : E → Option F) (hd : ∀ e, ρ (encode e) = some e) :
    ProjectsUnder I ρ (focusPrefix encode ρ a) a :=
  projectsUnder_focus encode ρ hd (fun w h hi =>
    let ⟨suffix, hs, _, _⟩ := ha w h hi; ⟨suffix, hs⟩)

theorem projectsPrefix_focus_other (encode : F → E) (decode : E → Option F)
    (ρ : E → Option G) (hd : ∀ e, ρ (encode e) = none) (he : ErasesPrefix a original) :
    ProjectsPrefix ρ id (focusPrefix encode decode a) (liftPrefix original) := by
  intro w h
  have ho := focusPrefix_other encode decode ρ hd a w h
  have hr := focusPrefix_erases encode decode he w h
  simp only [runPrefix_lift, hr, ho]
  cases original.run w <;> rfl

theorem ProjectsUnder.preserves (hg : ProjectsUnder I ρ g a)
    (ha : PrefixPreserves I S a) :
    ∀ w h, I (h.filterMap ρ) w → S ((runPrefix g w h).2.filterMap ρ) ∧
      match (runPrefix g w h).1 with
      | .error _ => True
      | .ok (_, v) => I ((runPrefix g w h).2.filterMap ρ) v := by
  intro w h hi
  obtain ⟨_, _, hs, hp⟩ := ha w (h.filterMap ρ) hi
  rw [hg w h hi] at hs hp
  exact ⟨hs, hp⟩

theorem projectsUnder_emit_bind (e : E) (he : ρ e = none)
    (hg : ProjectsUnder I ρ g a) : ProjectsUnder I ρ (do emitPrefix e; g) a := by
  intro w h hi
  simpa [runPrefix_bind, List.filterMap_append, he] using hg w (h ++ [e]) (by simpa [List.filterMap_append, he] using hi)

/-- A projection whose history is untouched on every outcome. -/
def HistoryFrame (ρ : E → Option F) (g : PrefixM E α) : Prop :=
  ∀ w h, (runPrefix g w h).2.filterMap ρ = h.filterMap ρ

theorem HistoryFrame.lift (ρ : E → Option F) (a : M α) : HistoryFrame ρ (liftPrefix a) := fun _ _ => rfl
theorem HistoryFrame.pure (ρ : E → Option F) (x : α) : HistoryFrame ρ (pure x) := fun _ _ => rfl
theorem HistoryFrame.emit (e : E) (he : ρ e = none) : HistoryFrame ρ (emitPrefix e) := by
  intro w h; simp [List.filterMap_append, he]
theorem HistoryFrame.bind (hg : HistoryFrame ρ g) (hf : ∀ x, HistoryFrame ρ (f x)) :
    HistoryFrame ρ (g >>= f) := by
  intro w h
  rw [runPrefix_bind]
  cases hr : runPrefix g w h with
  | mk result hist =>
    have hh := hg w h
    simp only [hr] at hh
    cases result with
    | error e => exact hh
    | ok out => exact (hf out.1 out.2 hist).trans hh
theorem HistoryFrame.project (hg : HistoryFrame ρ g) (he : ErasesPrefix g original) :
    ProjectsPrefix ρ id g (liftPrefix original) := by
  intro w h
  rw [runPrefix_lift, hg w h, he w h]
  cases original.run w <;> rfl

theorem HistoryFrame.forIn (xs : List γ) (b : β)
    (f : γ → β → PrefixM E (ForInStep β)) (hf : ∀ x b, HistoryFrame ρ (f x b)) :
    HistoryFrame ρ (ForIn.forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact HistoryFrame.pure ρ b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply HistoryFrame.bind (hf x b)
    intro step
    cases step with
    | done b => exact HistoryFrame.pure ρ b
    | yield b => exact ih b

/-- Unconditional history extension, without an endpoint or safety premise. -/
def Appends (a : PrefixM E α) : Prop :=
  ∀ w h, ∃ s, (runPrefix a w h).2 = h ++ s

theorem Appends.pure (x : α) : Appends (pure x : PrefixM E α) :=
  fun _ _ => ⟨[], (List.append_nil _).symm⟩
theorem Appends.lift (a : M α) : Appends (liftPrefix a : PrefixM E α) :=
  fun _ _ => ⟨[], (List.append_nil _).symm⟩
theorem Appends.focus (encode : F → E) (decode : E → Option F) (a : PrefixM F α) :
    Appends (focusPrefix encode decode a) := fun _ _ => ⟨_, rfl⟩
theorem Appends.bind (ha : Appends a) (hf : ∀ x, Appends (f x)) : Appends (a >>= f) := by
  intro w h
  obtain ⟨s, hs⟩ := ha w h
  rw [runPrefix_bind]
  cases hr : runPrefix a w h with
  | mk result hist =>
    simp only [hr] at hs
    cases result with
    | error e => exact ⟨s, hs⟩
    | ok out =>
      obtain ⟨t, ht⟩ := hf out.1 out.2 hist
      exact ⟨s ++ t, by simpa only [hs, List.append_assoc] using ht⟩
theorem Appends.forIn (xs : List γ) (b : β) (f : γ → β → PrefixM E (ForInStep β))
    (hf : ∀ x b, Appends (f x b)) : Appends (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact Appends.pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply Appends.bind (hf x b)
    intro step
    cases step with
    | done b => exact Appends.pure b
    | yield b => exact ih b
theorem Appends.range (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → PrefixM E (ForInStep β)) (hf : ∀ x b, Appends (f x b)) :
    Appends (ForIn.forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Appends.forIn _ b f hf

theorem Appends.project_focus (ha : Appends a) (encode : F → E) (ρ : E → Option F)
    (hd : ∀ e, ρ (encode e) = some e) :
    ProjectsPrefix ρ id (focusPrefix encode ρ a) a := by
  intro w h
  have hp := projectsUnder_focus (I := fun _ _ => True) encode ρ hd (fun w h _ => ha w h) w h trivial
  cases hr : (runPrefix (focusPrefix encode ρ a) w h).1 <;>
    simpa only [hr, Except.map, id] using hp

end Leanux.Proofs.Logged
