import Leanux.Proofs.WG.Lifetimes.Actions

/-! Equality frames for arbitrary views of the original World. A smaller
view inherits a frame by a pure projection; operational proofs are shared. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do Leanux.Proofs.WG.Lifetimes

abbrev SameView (view : World → σ) (a : M α) : Prop :=
  ProjectedAction view (fun s t => t = s) a

variable {σ τ α β : Type} {view : World → σ} {other : World → τ}
  {a : M α} {f : α → M β}

theorem SameView.wp (h : SameView view a) (P : σ → Prop) :
    ⦃fun w => ⌜P (view w)⌝⦄ a ⦃⇓? _ w => ⌜P (view w)⌝⦄ :=
  ProjectedAction.wp h P (fun _ _ he hp => he ▸ hp)

theorem SameView.of_wp (view : World → σ) (a : M α)
    (h : ∀ s, ⦃fun w => ⌜view w = s⌝⦄ a
      ⦃⇓? _ w => ⌜view w = s⌝⦄) : SameView view a :=
  ProjectedAction.of_wp view (fun s t => t = s) a h

theorem SameView.factor (h : SameView view a) (f : σ → τ) :
    SameView (fun w => f (view w)) a :=
  fun w x w' hr => congrArg f (h w x w' hr)

theorem SameView.of_factor (h : SameView view a) (f : σ → τ)
    (small : World → τ) (hf : ∀ w, small w = f (view w)) : SameView small a := by
  intro w x w' hr
  rw [hf w', hf w]
  exact congrArg f (h w x w' hr)

theorem SameView.of_sameKernel (view : Kernel → σ) (h : SameKernel a) :
    SameView (fun w => view w.k) a :=
  fun w x w' hr => congrArg view (h w x w' hr)

theorem SameView.product (h : SameView view a) (g : SameView other a) :
    SameView (fun w => (view w, other w)) a := by
  intro w x w' hr
  exact Prod.ext (h w x w' hr) (g w x w' hr)

theorem SameView.pure (view : World → σ) (x : α) : SameView view (pure x) := by
  intro w y w' hr
  cases hr
  rfl

theorem SameView.bind (ha : SameView view a) (hf : ∀ x, SameView view (f x)) :
    SameView view (a >>= f) := by
  intro w y w' hr
  simp only [StateT.run_bind] at hr
  cases hx : a.run w with
  | error e => simp [hx] at hr
  | ok v =>
    simp only [hx, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    exact (hf v.1 v.2 y w' hr).trans (ha w v.1 v.2 hx)

theorem SameView.map (h : SameView view a) (f : α → β) :
    SameView view (StateT.map f a) := by
  intro w y w' hr
  change (a.run w >>= fun out => Except.ok (f out.1, out.2)) = .ok (y, w') at hr
  cases hx : a.run w with
  | error e => simp [hx] at hr
  | ok v =>
    rcases v with ⟨x, u⟩
    simp [hx] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact h w x u hx

end Leanux.Proofs.Framing
