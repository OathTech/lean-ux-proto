import Leanux.Proofs.WG.Roaming.PublicationFrames
import Leanux.WG.PrevQueue

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Stronger-kernel variant of `PrevQueue_peek_spec`
(and `PrevQueue_peek_sameSnapshot`) in `WG/Keypairs/Frames/WGBase.lean`: this local obligation includes
the receive-packet store absent from the shared keypair snapshot. -/
theorem PrevQueue_peek_spec_kernel_variant {α : Type} (q : PrevQueue α) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ q.peek ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [PrevQueue.peek, PrevQueue.dequeue, branch, invariant, unsupported]

theorem read_get : Campaign2.read = (do
    let w ← get
    pure (Campaign2.snapshot w)) := rfl

end Leanux.Proofs.WG.Roaming
