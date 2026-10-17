import Leanux.Proofs.WG.TimerDiscipline.FireRetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem timerSelection_kernel_spec (P : Kernel → Prop) (worker : Worker) (jHi : UInt64) :
    ⦃fun w => ⌜P w.k⌝⦄ timerSelection worker jHi ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hp := peekUnit_spec_kernel_variant P worker
  mvcgen [timerSelection, getDev, getK, invariant, unsupported, hp]


end Leanux.Proofs.WG.TimerDiscipline
