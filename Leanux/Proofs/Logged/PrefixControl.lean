import Leanux.Proofs.Logged.Prefix

/-! An action that always stops has no continuation. These laws retain the
original state-dependent error and unchanged history without duplicating
unreachable suffixes after each input rejection. -/
namespace Leanux.Proofs.Logged
open Leanux
variable {Event α β : Type} {I : List Event → World → Prop} {S : List Event → Prop}

theorem erasesPrefix_lift_failure_bind (a : M α)
    (ha : ∀ w, ∃ e, a.run w = .error e)
    (g : α → PrefixM Event β) (f : α → M β) :
    ErasesPrefix (liftPrefix a >>= g) (a >>= f) := by
  intro w h
  obtain ⟨e, he⟩ := ha w
  simp [runPrefix_bind, he, StateT.run_bind]

theorem PrefixPreserves.lift_failure_bind
    (hs : ∀ h w, I h w → S h) (a : M α)
    (ha : ∀ w, ∃ e, a.run w = .error e) (g : α → PrefixM Event β) :
    PrefixPreserves I S (liftPrefix a >>= g) := by
  intro w h hi
  obtain ⟨e, he⟩ := ha w
  exact ⟨[], by simp [runPrefix_bind, he], by simpa [runPrefix_bind, he] using hs h w hi,
    by simp [runPrefix_bind, he]⟩

end Leanux.Proofs.Logged
