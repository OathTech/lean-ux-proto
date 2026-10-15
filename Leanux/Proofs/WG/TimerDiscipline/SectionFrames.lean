import Leanux.Proofs.WG.TimerDiscipline.FireSource
import Leanux.Proofs.WG.Noise.KernelFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The section wrapper preserves any callback contract on the kernel state.
Both actual hidden section reads still execute and may stop the run. -/
theorem runWorker_kernel_contract (worker : Worker) (body : M Unit)
    (P Q : Kernel → Prop)
    (contract : ⦃fun w => ⌜P w.k⌝⦄ body ⦃⇓? _ w => ⌜Q w.k⌝⦄) :
    ⦃fun w => ⌜P w.k⌝⦄ runWorker worker body ⦃⇓? _ w => ⌜Q w.k⌝⦄ := by
  have hs := hidden_kernel_spec P (.sectionStart worker)
  have he := hidden_kernel_spec Q (.sectionStop worker)
  mvcgen [runWorker, hs, he, contract]

theorem runTimerSection_kernel_contract (worker : Worker) (body : M Unit)
    (P Q : Kernel → Prop)
    (contract : ⦃fun w => ⌜P w.k⌝⦄ body ⦃⇓? _ w => ⌜Q w.k⌝⦄) :
    ⦃fun w => ⌜P w.k⌝⦄ runTimerSection worker body ⦃⇓? _ w => ⌜Q w.k⌝⦄ := by
  have hr := runWorker_kernel_contract worker body P Q contract
  mvcgen [runTimerSection, invariant, hr]


end Leanux.Proofs.WG.TimerDiscipline
