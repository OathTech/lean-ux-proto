import Leanux.Proofs.Logged.FocusComposition
import Leanux.Proofs.Logged.PrefixLoops

/-! Focused preservation for arbitrary journal/state invariants. The lower
observer must append on every input, including Stop; no history independence
is assumed. Existing focus equalities supply the composition laws. -/
namespace Leanux.Proofs.Logged
open Leanux
variable {E F State α β γ : Type}

def FocusedInvariant (I : List F → State → Prop) (S : List F → Prop)
    (encode : E → F) (decode : F → Option E) (g : PrefixT E State α) : Prop :=
  Appends g ∧ PrefixPreserves I S (focusPrefix encode decode g)

theorem prefixPreserves_congr (hg : PrefixPreserves I S g)
    (eq : ∀ w h, runPrefix g w h = runPrefix f w h) : PrefixPreserves I S f := by
  intro w h hi
  simpa only [← eq w h] using hg w h hi

theorem FocusedInvariant.bind (inverse : ∀ e, decode (encode e) = some e)
    (hg : FocusedInvariant I S encode decode g)
    (hf : ∀ x, FocusedInvariant I S encode decode (f x)) :
    FocusedInvariant I S encode decode (g >>= f) :=
  ⟨hg.1.bind (fun x => (hf x).1),prefixPreserves_congr
    (hg.2.bind (fun x => (hf x).2))
    (focusPrefix_bind_appends encode decode inverse hg.1 (fun x => (hf x).1))⟩

theorem FocusedInvariant.pure (encode : E → F) (decode : F → Option E)
    (safe : ∀ h w, I h w → S h) (x : α) :
    FocusedInvariant I S encode decode (pure x) := by
  refine ⟨Appends.pure x,?_⟩
  apply prefixPreserves_congr (PrefixPreserves.pure safe x)
  intro w h
  change (Except.ok (ε := Stop) (x,w),h) =
    (.ok (x,w),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

theorem FocusedInvariant.lift (encode : E → F) (decode : F → Option E)
    (a : StateT State (Except Stop) α)
    (ha : PrefixPreserves I S (liftPrefix a)) :
    FocusedInvariant I S encode decode (liftPrefix a) := by
  refine ⟨Appends.lift a,?_⟩
  apply prefixPreserves_congr ha
  intro w h
  change (a.run w,h) =
    (a.run w,h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

theorem FocusedInvariant.ite (p : Prop) [Decidable p]
    (ha : p → FocusedInvariant I S encode decode a)
    (hb : ¬p → FocusedInvariant I S encode decode b) :
    FocusedInvariant I S encode decode (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem FocusedInvariant.forIn (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h) (xs : List α) (init : β)
    (f : α → β → PrefixT E State (ForInStep β))
    (hf : ∀ x b, FocusedInvariant I S encode decode (f x b)) :
    FocusedInvariant I S encode decode (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact FocusedInvariant.pure encode decode safe init
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply (hf x init).bind inverse
    intro step
    cases step with
    | done b => exact FocusedInvariant.pure encode decode safe b
    | yield b => exact ih b

theorem FocusedInvariant.range (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h) (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → PrefixT E State (ForInStep β))
    (hf : ∀ x b, FocusedInvariant I S encode decode (f x b)) :
    FocusedInvariant I S encode decode (ForIn.forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact FocusedInvariant.forIn encode decode inverse safe _ init f hf

end Leanux.Proofs.Logged
