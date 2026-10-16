import Leanux.Kernel.Defs
import Std.Tactic.Do

/-! Partial endpoint contracts over the actual StateT stack. The outer-state
predicate does not restrict the inner state. Native execution bridges below
quantify every ambient input and output; no old-world representation is used. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

section Generic
variable {σ α β : Type} {m : Type → Type} {ps : PostShape}
  [Monad m] [WPMonad m ps]

def Hoare (action : StateT σ m α) (pre : σ → Prop)
    (post : α → σ → Prop) : Prop :=
  Triple action (fun s => ⌜pre s⌝) (⇓? x s => ⌜post x s⌝)

def Preserves (pre : σ → Prop) (action : StateT σ m α) : Prop :=
  Hoare action pre (fun _ => pre)

theorem hoare_iff_triple (a : StateT σ m α) (P : σ → Prop) (Q : α → σ → Prop) :
    Hoare a P Q ↔ ⦃fun s => ⌜P s⌝⦄ a ⦃⇓? x s => ⌜Q x s⌝⦄ := Iff.rfl

theorem hoare_pure (a : α) (P : σ → Prop) :
    Hoare (pure a : StateT σ m α) P (fun b s => b = a ∧ P s) := by
  apply Triple.pure
  intro s
  exact SPred.pure_mono (fun h => ⟨rfl, h⟩)

theorem hoare_bind (a : StateT σ m α) (f : α → StateT σ m β)
    (ha : Hoare a P Q) (hf : ∀ x, Hoare (f x) (Q x) R) :
    Hoare (a >>= f) P R := Triple.bind a f ha hf

theorem hoare_consequence {a : StateT σ m α} (h : Hoare a P Q)
    (hp : ∀ s, P' s → P s) (hq : ∀ x s, Q x s → Q' x s) :
    Hoare a P' Q' := by
  apply Triple.entails_wp_of_pre_post h
  · intro s; exact SPred.pure_mono (hp s)
  · exact ⟨fun x s => SPred.pure_mono (hq x s), ExceptConds.entails.refl _⟩

theorem preserves_bind {a : StateT σ m α} {f : α → StateT σ m β}
    (ha : Preserves P a) (hf : ∀ x, Preserves P (f x)) :
    Preserves P (a >>= f) := hoare_bind a f ha hf

theorem preserves_pure (a : α) : Preserves P (pure a : StateT σ m α) :=
  hoare_consequence (hoare_pure a P) (fun _ h => h) (fun _ _ h => h.2)

theorem hoare_get (P : σ → Prop) :
    Hoare (get : StateT σ m σ) P (fun v s => v = s ∧ P s) := by
  unfold Hoare
  mvcgen

theorem hoare_modify (f : σ → σ) (h : ∀ s, P s → Q () (f s)) :
    Hoare (modify f : StateT σ m Unit) P Q := by
  unfold Hoare
  mvcgen
  apply SPred.pure_intro
  apply h
  assumption

end Generic

/-- A local exception rule without the bundled rule's unused parameters. -/
@[spec high] theorem except_throw_wp {ε α : Type} (e : ε)
    (Q : PostCond α (.except ε .pure)) :
    Triple (ps := .except ε .pure) (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) Q := by
  simp [Triple.iff]

/-- Partial correctness is exactly the normal native execution contract. -/
theorem hoare_iff_run (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) :
    Hoare a P Q ↔
      ∀ s x s', P s → a.run s = .ok (x, s') → Q x s' := by
  constructor
  · intro h s x s' hp hr
    have hh := h s hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh
  · intro h s hp
    cases hr : a.run s with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      rcases out with ⟨x, s'⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h s x s' hp hr

/-- Total correctness requires an actual successful native execution. -/
theorem total_iff_run (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) :
    (⦃fun s => ⌜P s⌝⦄ a ⦃⇓ x s => ⌜Q x s⌝⦄) ↔
      ∀ s, P s → ∃ x s', a.run s = .ok (x, s') ∧ Q x s' := by
  constructor
  · intro h s hp
    have hh := h s hp
    cases hr : a.run s with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      rcases out with ⟨x, s'⟩
      refine ⟨x, s', rfl, ?_⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh
  · intro h s hp
    obtain ⟨x, s', hr, hq⟩ := h s hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq

/-- Partial correctness is exactly the normal native execution contract. -/
theorem hoare_iff_run_ambient (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) :
    Hoare a P Q ↔
      ∀ s ambient x s' ambient', P s → (a.run s).run ambient = .ok ((x, s'), ambient') → Q x s' := by
  constructor
  · intro h s ambient x s' ambient' hp hr
    have hh := h s ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh
  · intro h s ambient hp
    cases hr : (a.run s).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      rcases out with ⟨⟨x, s'⟩, ambient'⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h s ambient x s' ambient' hp hr

/-- Total correctness requires an actual successful native execution. -/
theorem total_iff_run_ambient (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) :
    (⦃fun s => ⌜P s⌝⦄ a ⦃⇓ x s => ⌜Q x s⌝⦄) ↔
      ∀ s ambient, P s → ∃ x s' ambient', (a.run s).run ambient = .ok ((x, s'), ambient') ∧ Q x s' := by
  constructor
  · intro h s ambient hp
    have hh := h s ambient hp
    cases hr : (a.run s).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      rcases out with ⟨⟨x, s'⟩, ambient'⟩
      refine ⟨x, s', ambient', rfl, ?_⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh
  · intro h s ambient hp
    obtain ⟨x, s', ambient', hr, hq⟩ := h s ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq

/-- Partial correctness is exactly the normal native execution contract. -/
theorem hoare_iff_run_task (a : StateT σ TaskM α) (P : σ → Prop) (Q : α → σ → Prop) :
    Hoare a P Q ↔
      ∀ s tasks ambient x s' tasks' ambient', P s → ((a.run s).run tasks).run ambient = .ok (((x, s'), tasks'), ambient') → Q x s' := by
  constructor
  · intro h s tasks ambient x s' tasks' ambient' hp hr
    have hh := h s tasks ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh
  · intro h s tasks ambient hp
    cases hr : ((a.run s).run tasks).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      rcases out with ⟨⟨⟨x, s'⟩, tasks'⟩, ambient'⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h s tasks ambient x s' tasks' ambient' hp hr

/-- Total correctness requires an actual successful native execution. -/
theorem total_iff_run_task (a : StateT σ TaskM α) (P : σ → Prop) (Q : α → σ → Prop) :
    (⦃fun s => ⌜P s⌝⦄ a ⦃⇓ x s => ⌜Q x s⌝⦄) ↔
      ∀ s tasks ambient, P s → ∃ x s' tasks' ambient', ((a.run s).run tasks).run ambient = .ok (((x, s'), tasks'), ambient') ∧ Q x s' := by
  constructor
  · intro h s tasks ambient hp
    have hh := h s tasks ambient hp
    cases hr : ((a.run s).run tasks).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      rcases out with ⟨⟨⟨x, s'⟩, tasks'⟩, ambient'⟩
      refine ⟨x, s', tasks', ambient', rfl, ?_⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh
  · intro h s tasks ambient hp
    obtain ⟨x, s', tasks', ambient', hr, hq⟩ := h s tasks ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq

theorem hoare_throw (e : Stop) :
    Hoare (throw e : StateT σ (Except Stop) α) P Q := by
  apply (hoare_iff_run _ _ _).mpr
  intro s x s' hp hr
  cases hr

end Leanux.Proofs.Framing
