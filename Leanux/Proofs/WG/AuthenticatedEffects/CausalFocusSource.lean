import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! Exact focus-distribution facts for extending an existing observer. These
retain its full event history and result, including stopped continuations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalFocus
open Leanux Leanux.Proofs.Logged
variable {E F State α β : Type}

def Aligned (encode : E → F) (decode : F → Option E)
    (g : PrefixT F State α) (t : PrefixT E State α) : Prop :=
  Appends t ∧ g = focusPrefix encode decode t

theorem native (encode : E → F) (decode : F → Option E) (t : PrefixT E State α) (ht : Appends t) :
    Aligned encode decode (focusPrefix encode decode t) t := ⟨ht,rfl⟩

theorem pure (encode : E → F) (decode : F → Option E) (x : α) :
    Aligned encode decode (Pure.pure x : PrefixT F State α) (Pure.pure x) := by
  refine ⟨Appends.pure x,?_⟩
  funext w h
  change (Except.ok (ε := Stop) (x,w),h) = (Except.ok (ε := Stop) (x,w),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

theorem bind (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    {g : PrefixT F State α} {t : PrefixT E State α}
    {f : α → PrefixT F State β} {b : α → PrefixT E State β}
    (hg : Aligned encode decode g t) (hf : ∀ x, Aligned encode decode (f x) (b x)) :
    Aligned encode decode (g >>= f) (t >>= b) := by
  refine ⟨hg.1.bind (fun x => (hf x).1),?_⟩
  rw [hg.2]
  have same : f = fun x => focusPrefix encode decode (b x) := funext (fun x => (hf x).2)
  rw [same]
  funext w h
  exact focusPrefix_bind_appends encode decode inverse hg.1 (fun x => (hf x).1) w h

theorem choice (encode : E → F) (decode : F → Option E) (p : Prop) [Decidable p]
    {g k : PrefixT F State α} {t b : PrefixT E State α}
    (hg : p → Aligned encode decode g t) (hk : ¬p → Aligned encode decode k b) :
    Aligned encode decode (if p then g else k) (if p then t else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hg hp
  · exact hk hp

theorem capture (encode : E → F) (decode : F → Option E)
    {g : PrefixM F α} {t : PrefixM E α} (hg : Aligned encode decode g t) :
    Aligned encode decode (captureObserved g) (captureObserved t) := by
  refine ⟨hg.1.captureObserved,?_⟩
  rw [hg.2]
  funext w h
  change runPrefix (captureObserved (focusPrefix encode decode t)) w h =
    runPrefix (focusPrefix encode decode (captureObserved t)) w h
  rw [runPrefix_captureObserved]
  change _ = ((runPrefix (captureObserved t) w (h.filterMap decode)).1,
    h ++ ((runPrefix (captureObserved t) w (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode)
  rw [runPrefix_captureObserved]
  rfl

theorem loop (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e) (xs : List α) (initial : β)
    (g : α → β → PrefixT F State (ForInStep β)) (t : α → β → PrefixT E State (ForInStep β))
    (hg : ∀ x b, Aligned encode decode (g x b) (t x b)) :
    Aligned encode decode (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => exact pure encode decode initial
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply bind encode decode inverse (hg x initial)
    intro step
    cases step with
    | done b => exact pure encode decode b
    | yield b => exact ih b

end Leanux.Proofs.WG.AuthenticatedEffects.CausalFocus
