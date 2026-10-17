import Leanux.Proofs.WG.Noise.Basic
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem read_snapshot (P : World → Prop) :
    ⦃fun w => ⌜P w⌝⦄ Campaign2.read
      ⦃⇓? result w => ⌜result = Campaign2.snapshot w ∧ P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  change Except.ok (Campaign2.snapshot w, w) = Except.ok (result, final) at run
  cases run
  exact ⟨rfl, pre⟩

end Leanux.Proofs.WG.Roaming
