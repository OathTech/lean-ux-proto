import Leanux.Proofs.Framing.Projection

/-! Projection-parametric finite-loop and map rules over actual StateT stacks,
and checked references to constants in the pinned mirror. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

variable {S σ : Type} {m : Type → Type} {ps : PostShape}
  [Monad m] [WPMonad m ps]

def normalizePinnedName : Lean.Name → Lean.Name
  | .str p "0" => .num (normalizePinnedName p) 0
  | .str p s => .str (normalizePinnedName p) s
  | .num p n => .num (normalizePinnedName p) n
  | .anonymous => .anonymous

/-- A checked reference to a constant in the pinned mirror, including its
private numeric name component. It introduces no new definition or assumption. -/
macro "pinned_const " n:ident : term =>
  pure (Lean.mkCIdent (normalizePinnedName n.getId))

theorem list_view_spec (view : S → σ) (P : σ → Prop) {α β : Type}
    (xs : List α) (init : β) (f : α → β → StateT S m (ForInStep β))
    (hf : ∀ x b, ⦃fun w => ⌜P (view w)⌝⦄ f x b
      ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ forIn xs init f
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  let inv : PostCond β (.arg S ps) :=
    (⇓? _ w => ⌜P (view w)⌝)
  change Triple (forIn xs init f) (inv.1 init) inv
  refine Std.Do.Spec.forIn_list_const_inv (inv := inv) ?_
  intro x b
  apply Triple.entails_wp_of_post (hf x b)
  constructor
  · intro r
    cases r <;> exact .rfl
  · exact .rfl

theorem map_view_spec (view : S → σ) (P : σ → Prop) {α β : Type}
    (f : α → β) (a : StateT S m α)
    (ha : ⦃fun w => ⌜P (view w)⌝⦄ a ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ StateT.map f a
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  exact Std.Do.Spec.map' ha

theorem discard_view_spec (view : S → σ) (P : σ → Prop) {α : Type} (a : StateT S m α)
    (ha : ⦃fun w => ⌜P (view w)⌝⦄ a ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ discard a
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := map_view_spec view P (fun _ => ()) a ha


end Leanux.Proofs.Framing
