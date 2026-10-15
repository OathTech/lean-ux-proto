import Leanux.Proofs.WG.TimerDiscipline.FireRetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Kernel-state variant of shared Keypairs.Frames.peekUnit_spec, local while
campaign 1 owns the shared-frame carry. Ambient records may still be consumed. -/
theorem peekUnit_spec_kernel_variant (P : Kernel → Prop) (worker : Worker) :
    ⦃fun w => ⌜P w.k⌝⦄ peekUnit worker ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [peekUnit, skipAmbient]

theorem timerSelection_kernel_spec (P : Kernel → Prop) (worker : Worker) (jHi : UInt64) :
    ⦃fun w => ⌜P w.k⌝⦄ timerSelection worker jHi ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hp := peekUnit_spec_kernel_variant P worker
  mvcgen [timerSelection, getDev, getK, invariant, unsupported, hp]


end Leanux.Proofs.WG.TimerDiscipline
