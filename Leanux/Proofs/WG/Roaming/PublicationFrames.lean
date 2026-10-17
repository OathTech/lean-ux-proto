import Leanux.Proofs.WG.Noise.Basic
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Reading an observation preserves an arbitrary predicate of the entire input.
Specialize the state and observation to the actual product snapshot at callers. -/
theorem read_snapshot {σ α : Type} (P : σ → Prop) (observe : σ → α) :
    ⦃fun w => ⌜P w⌝⦄ ((do let w ← get; pure (observe w)) : StateT σ (Except Stop) α)
      ⦃⇓? result w => ⌜result = observe w ∧ P w⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w result final pre run
  change Except.ok (observe w, w) = Except.ok (result, final) at run
  cases run
  exact ⟨rfl, pre⟩

end Leanux.Proofs.WG.Roaming
