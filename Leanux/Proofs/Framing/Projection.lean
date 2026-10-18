import Leanux.Proofs.WG.Lifetimes.Actions

/-! Equality frames for views of an actual outer StateT state. A smaller view
inherits a frame by pure projection, independent of the inner monad's shape. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do Leanux.Proofs.WG.Lifetimes

variable {S σ τ α β : Type} {m : Type → Type} {ps : PostShape}
  [Monad m] [WPMonad m ps]

abbrev SameView (view : S → σ) (a : StateT S m α) : Prop :=
  ProjectedAction view (fun s t => t = s) a

variable {view : S → σ} {other : S → τ}
  {a : StateT S m α} {f : α → StateT S m β}

theorem SameView.wp (h : SameView view a) (P : σ → Prop) :
    ⦃fun s => ⌜P (view s)⌝⦄ a ⦃⇓? _ s => ⌜P (view s)⌝⦄ :=
  ProjectedAction.wp h P (fun _ _ he hp => he ▸ hp)

theorem SameView.of_wp (view : S → σ) (a : StateT S m α)
    (h : ∀ initial, ⦃fun s => ⌜view s = initial⌝⦄ a
      ⦃⇓? _ s => ⌜view s = initial⌝⦄) : SameView view a :=
  ProjectedAction.of_wp view (fun s t => t = s) a h

theorem SameView.factor (h : SameView view a) (f : σ → τ) :
    SameView (fun s => f (view s)) a := by
  apply SameView.of_wp
  intro initial
  exact h.wp (fun v => f v = initial)

theorem SameView.of_factor (h : SameView view a) (f : σ → τ)
    (small : S → τ) (hf : ∀ s, small s = f (view s)) : SameView small a := by
  have he : small = fun s => f (view s) := funext hf
  rw [he]
  exact h.factor f

theorem SameView.product (h : SameView view a) (g : SameView other a) :
    SameView (fun s => (view s, other s)) a := by
  intro initial
  apply Triple.entails_wp_of_pre_post (Triple.and a (h initial.1) (g initial.2))
  · intro s
    exact SPred.and_intro
      (SPred.pure_mono (fun he => congrArg Prod.fst he))
      (SPred.pure_mono (fun he => congrArg Prod.snd he))
  · constructor
    · intro x s
      exact SPred.pure_and.mp.trans (SPred.pure_mono (fun he => Prod.ext he.1 he.2))
    · exact ExceptConds.entails_true

theorem SameView.pure (view : S → σ) (x : α) :
    SameView view (pure x : StateT S m α) := by
  intro initial
  exact preserves_pure (P := fun s => view s = initial) x

theorem SameView.bind (ha : SameView view a) (hf : ∀ x, SameView view (f x)) :
    SameView view (a >>= f) := by
  intro initial
  exact preserves_bind (ha initial) (fun x => hf x initial)

theorem SameView.map (h : SameView view a) (f : α → β) :
    SameView view (StateT.map f a) := by
  intro initial
  exact Std.Do.Spec.map' (h initial)

end Leanux.Proofs.Framing
