import Leanux.Proofs.WG.Lifetimes.Store
import Leanux.Proofs.Framing.Hoare

/-! Reusable partial execution contracts over the actual StateT stack.
Relations observe the outer state. Native execution bridges quantify every
Ambient endpoint, and finite execution chains carry that endpoint onward. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Std.Do Leanux.Proofs.Framing

section Generic
variable {S σ α β : Type} {m : Type → Type} {ps : PostShape}
  [Monad m] [WPMonad m ps]

def Action (P : S → Prop) (R : S → S → Prop) (a : StateT S m α) : Prop :=
  ∀ start, Hoare a (fun s => s = start ∧ P s) (fun _ s => P s ∧ R start s)

/-- Freeze the relevant projection in a partial WP contract. The inner state
is unrestricted; predicates that observe it require a multistate Triple. -/
def ProjectedAction (project : S → σ) (R : σ → σ → Prop)
    (a : StateT S m α) : Prop :=
  ∀ initial, Hoare a (fun s => project s = initial) (fun _ s => R initial (project s))

variable {P : S → Prop} {R : S → S → Prop}
  {a : StateT S m α} {f : α → StateT S m β}

theorem ProjectedAction.of_wp (project : S → σ) (R : σ → σ → Prop) (a : StateT S m α)
    (h : ∀ initial, ⦃fun s => ⌜project s = initial⌝⦄ a
      ⦃⇓? _ s => ⌜R initial (project s)⌝⦄) : ProjectedAction project R a := h

theorem ProjectedAction.wp {project : S → σ} {R : σ → σ → Prop}
    (h : ProjectedAction project R a)
    (P : σ → Prop) (hp : ∀ s t, R s t → P s → P t) :
    ⦃fun s => ⌜P (project s)⌝⦄ a ⦃⇓? _ s => ⌜P (project s)⌝⦄ := by
  intro s
  apply SPred.pure_elim'
  intro hs
  have hc : Hoare a (fun t => project t = project s) (fun _ t => P (project t)) :=
    hoare_consequence (h (project s)) (fun _ he => he)
      (fun _ t hr => hp _ _ hr hs)
  exact (SPred.pure_intro rfl).trans (hc s)

theorem ProjectedAction.action {project : S → σ} {R : σ → σ → Prop}
    (h : ProjectedAction project R a)
    (P : σ → Prop) (hp : ∀ s t, R s t → P s → P t) :
    Action (fun s => P (project s)) (fun s t => R (project s) (project t)) a := by
  intro start s
  apply SPred.pure_elim'
  rintro ⟨he, hs⟩
  subst s
  have hc : Hoare a (fun t => project t = project start)
      (fun _ t => P (project t) ∧ R (project start) (project t)) :=
    hoare_consequence (h (project start)) (fun _ he => he)
      (fun _ t hr => ⟨hp _ _ hr hs, hr⟩)
  exact (SPred.pure_intro rfl).trans (hc start)

theorem Action.pure (hrefl : ∀ s, R s s) (x : α) :
    Action P R (pure x : StateT S m α) := by
  intro start
  apply hoare_consequence (hoare_pure x (fun s => s = start ∧ P s))
  · exact fun _ h => h
  · intro _ s h
    refine ⟨h.2.2, ?_⟩
    rw [← h.2.1]
    exact hrefl s

theorem Action.bind (htrans : ∀ u v w, R u v → R v w → R u w)
    (ha : Action P R a) (hf : ∀ x, Action P R (f x)) :
    Action P R (a >>= f) := by
  intro start
  apply hoare_bind a f (ha start)
  intro x middle
  apply SPred.pure_elim'
  rintro ⟨hp, hr⟩
  have hc : Hoare (f x) (fun s => s = middle ∧ P s)
      (fun _ s => P s ∧ R start s) :=
    hoare_consequence (hf x middle) (fun _ h => h)
      (fun _ s h => ⟨h.1, htrans _ _ _ hr h.2⟩)
  exact (SPred.pure_intro ⟨rfl, hp⟩).trans (hc middle)

theorem Action.wp (h : Action P R a) (start : S) :
    ⦃fun s => ⌜s = start ∧ P s⌝⦄ a
    ⦃⇓? _ s => ⌜P s ∧ R start s⌝⦄ := h start

theorem Action.of_wp (a : StateT S m α)
    (h : ∀ start, ⦃fun s => ⌜s = start ∧ P s⌝⦄ a
      ⦃⇓? _ s => ⌜P s ∧ R start s⌝⦄) : Action P R a := h

end Generic

/-- The base-stack contract is exactly its successful native endpoints. -/
theorem Action.iff_run (P : S → Prop) (R : S → S → Prop)
    (a : StateT S (Except Stop) α) :
    Action P R a ↔ ∀ s x s', P s → a.run s = .ok (x, s') → P s' ∧ R s s' := by
  constructor
  · intro h s x s' hp hr
    exact (hoare_iff_run _ _ _).mp (h s) s x s' ⟨rfl, hp⟩ hr
  · intro h start
    apply (hoare_iff_run _ _ _).mpr
    rintro s x s' ⟨rfl, hp⟩ hr
    exact h s x s' hp hr

/-- No Ambient input or successful output is omitted from the native contract. -/
theorem Action.iff_run_ambient (P : S → Prop) (R : S → S → Prop)
    (a : StateT S AmbientM α) :
    Action P R a ↔ ∀ s ambient x s' ambient', P s →
      (a.run s).run ambient = .ok ((x, s'), ambient') → P s' ∧ R s s' := by
  constructor
  · intro h s ambient x s' ambient' hp hr
    exact (hoare_iff_run_ambient _ _ _).mp (h s) s ambient x s' ambient' ⟨rfl, hp⟩ hr
  · intro h start
    apply (hoare_iff_run_ambient _ _ _).mpr
    rintro s ambient x s' ambient' ⟨rfl, hp⟩ hr
    exact h s ambient x s' ambient' hp hr

theorem ProjectedAction.iff_run (project : S → σ) (R : σ → σ → Prop)
    (a : StateT S (Except Stop) α) :
    ProjectedAction project R a ↔
      ∀ s x s', a.run s = .ok (x, s') → R (project s) (project s') := by
  constructor
  · intro h s x s' hr
    exact (hoare_iff_run _ _ _).mp (h (project s)) s x s' rfl hr
  · intro h initial
    apply (hoare_iff_run _ _ _).mpr
    intro s x s' he hr
    rw [← he]
    exact h s x s' hr

theorem ProjectedAction.iff_run_ambient (project : S → σ) (R : σ → σ → Prop)
    (a : StateT S AmbientM α) :
    ProjectedAction project R a ↔ ∀ s ambient x s' ambient',
      (a.run s).run ambient = .ok ((x, s'), ambient') → R (project s) (project s') := by
  constructor
  · intro h s ambient x s' ambient' hr
    exact (hoare_iff_run_ambient _ _ _).mp (h (project s)) s ambient x s' ambient' rfl hr
  · intro h initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro s ambient x s' ambient' he hr
    rw [← he]
    exact h s ambient x s' ambient' hr

/-- A finite sequence names each actual helper and complete successful call.
The next call receives both native outputs of the preceding call. -/
inductive Executions (family : (α : Type) → StateT S AmbientM α → Prop) :
    S → Ambient → S → Ambient → Prop where
  | nil (s ambient) : Executions family s ambient s ambient
  | cons {α : Type} {a : StateT S AmbientM α} {x : α} {s middle finish : S}
      {ambient nextAmbient finalAmbient : Ambient}
      (ha : family α a)
      (hr : (a.run s).run ambient = .ok ((x, middle), nextAmbient))
      (tail : Executions family middle nextAmbient finish finalAmbient) :
      Executions family s ambient finish finalAmbient

variable {S : Type} {family : (α : Type) → StateT S AmbientM α → Prop}
  {P : S → Prop} {R : S → S → Prop} {s s' : S} {ambient ambient' : Ambient}

theorem Executions.contract (h : Executions family s ambient s' ambient')
    (hrefl : ∀ s, R s s) (htrans : ∀ u v w, R u v → R v w → R u w)
    (hc : ∀ {α} (a : StateT S AmbientM α), family α a → Action P R a) (hp : P s) :
    P s' ∧ R s s' := by
  induction h with
  | nil s ambient => exact ⟨hp, hrefl s⟩
  | cons ha hr tail ih =>
    have hs := (Action.iff_run_ambient _ _ _).mp (hc _ ha) _ _ _ _ _ hp hr
    have ht := ih hs.1
    exact ⟨ht.1, htrans _ _ _ hs.2 ht.2⟩

end Leanux.Proofs.WG.Lifetimes
