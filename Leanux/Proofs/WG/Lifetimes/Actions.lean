import Leanux.Proofs.WG.Lifetimes.Store
import Leanux.Proofs.Framing.WP

/-! Reusable execution contracts for projections. The relation and invariant
are parameters, so store identities and epoch preservation use the same
composition lemmas. Executions are successful calls of the original monad. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Std.Do Leanux.Proofs.Framing

def Action (P : World → Prop) (R : World → World → Prop) (a : M α) : Prop :=
  ∀ w x w', P w → a.run w = .ok (x, w') → P w' ∧ R w w'

/-- Projection contracts freeze only the relevant state in a WP proof, rather
than the full World. This supplies a reusable framing layer for each store. -/
def ProjectedAction (project : World → σ) (R : σ → σ → Prop) (a : M α) : Prop :=
  ∀ w x w', a.run w = .ok (x, w') → R (project w) (project w')

theorem ProjectedAction.of_wp (project : World → σ) (R : σ → σ → Prop) (a : M α)
    (h : ∀ s, ⦃fun w => ⌜project w = s⌝⦄ a
      ⦃⇓? _ w => ⌜R s (project w)⌝⦄) : ProjectedAction project R a := by
  intro w x w' hr
  exact (hoare_iff_triple _ _ _).mpr (h (project w)) w x w' rfl hr

theorem ProjectedAction.wp {project : World → σ} {R : σ → σ → Prop}
    (h : ProjectedAction project R a)
    (P : σ → Prop) (hp : ∀ s t, R s t → P s → P t) :
    ⦃fun w => ⌜P (project w)⌝⦄ a ⦃⇓? _ w => ⌜P (project w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hw hr
  exact hp _ _ (h w x w' hr) hw

theorem ProjectedAction.action {project : World → σ} {R : σ → σ → Prop}
    (h : ProjectedAction project R a)
    (P : σ → Prop) (hp : ∀ s t, R s t → P s → P t) :
    Action (fun w => P (project w)) (fun w v => R (project w) (project v)) a := by
  intro w x w' hw hr
  have ht := h w x w' hr
  exact ⟨hp _ _ ht hw, ht⟩

theorem Action.pure (hrefl : ∀ w, R w w) (x : α) : Action P R (pure x) := by
  intro w y w' hp hr
  cases hr
  exact ⟨hp, hrefl w⟩

theorem Action.bind (htrans : ∀ u v w, R u v → R v w → R u w)
    (ha : Action P R a) (hf : ∀ x, Action P R (f x)) :
    Action P R (a >>= f) := by
  intro w y w' hp hr
  simp only [StateT.run_bind] at hr
  cases hx : a.run w with
  | error e => simp [hx] at hr
  | ok v =>
    simp only [hx, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    have hfirst := ha w v.1 v.2 hp hx
    have hlast := hf v.1 v.2 y w' hfirst.1 hr
    exact ⟨hlast.1, htrans _ _ _ hfirst.2 hlast.2⟩

theorem Action.of_sameKernel (project : Kernel → σ)
    (P : σ → Prop) (R : σ → σ → Prop) (hrefl : ∀ s, R s s)
    (ha : SameKernel a) :
    Action (fun w => P (project w.k)) (fun w v => R (project w.k) (project v.k)) a := by
  intro w x w' hp hr
  dsimp only
  rw [ha w x w' hr]
  exact ⟨hp, hrefl _⟩

theorem Action.wp (h : Action P R a) (start : World) :
    ⦃fun w => ⌜w = start ∧ P w⌝⦄ a
    ⦃⇓? _ w => ⌜P w ∧ R start w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  simpa only [hp.1] using h w x w' hp.2 hr

theorem Action.of_wp (a : M α)
    (h : ∀ start, ⦃fun w => ⌜w = start ∧ P w⌝⦄ a
      ⦃⇓? _ w => ⌜P w ∧ R start w⌝⦄) : Action P R a := by
  intro w x w' hp hr
  exact (hoare_iff_triple _ _ _).mpr (h w) w x w' ⟨rfl, hp⟩ hr

/-- A finite sequence names each actual helper and its complete successful
execution. The family controls which helpers the theorem covers. -/
inductive Executions (family : (α : Type) → M α → Prop) : World → World → Prop where
  | nil (w) : Executions family w w
  | cons {α : Type} {a : M α} {x : α} {w v u : World}
      (ha : family α a) (hr : a.run w = .ok (x, v))
      (tail : Executions family v u) : Executions family w u

theorem Executions.contract (h : Executions family w w')
    (hrefl : ∀ w, R w w) (htrans : ∀ u v w, R u v → R v w → R u w)
    (hc : ∀ {α} (a : M α), family α a → Action P R a) (hp : P w) :
    P w' ∧ R w w' := by
  induction h with
  | nil w => exact ⟨hp, hrefl w⟩
  | cons ha hr tail ih =>
    have hs := hc _ ha _ _ _ hp hr
    have ht := ih hs.1
    exact ⟨ht.1, htrans _ _ _ hs.2 ht.2⟩

end Leanux.Proofs.WG.Lifetimes
