import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Peeking can discard ambient records, but preserves the device and unit associations. -/
theorem peekUnit_dispatch_frame (P : Kernel → List (Nat × Nat × Nat) → Prop) :
    ⦃fun w => ⌜P w.k w.unitPeers⌝⦄ peekUnit .sendWorker
      ⦃⇓? _ w => ⌜P w.k w.unitPeers⌝⦄ := by
  mvcgen [peekUnit, skipAmbient]

end Leanux.Proofs.WG.TimerDiscipline
