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

/-- The reference-count check emits decisions but does not write the kernel. -/
theorem refcountInc_kernel_frame (P : Kernel → Prop) (old : Nat) :
    ⦃fun w => ⌜P w.k⌝⦄ refcountInc old ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [refcountInc, branch, branchCmp, unsupported]

end Leanux.Proofs.WG.Roaming
