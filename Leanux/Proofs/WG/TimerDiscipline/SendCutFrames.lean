import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Kernel projection variant of shared WGFrames.loopbackSend_spec. -/
theorem loopbackSend_spec_kernel_variant (P : Kernel → Prop) (sites : List HiddenSite) (raised : Bool) :
    ⦃fun w => ⌜P w.k⌝⦄ loopbackSend sites raised ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hc := skipCut_spec_kernel_variant P
  have hh := hidden_kernel_spec P
  mvcgen [loopbackSend, raiseLoopbackRx, loopbackSoftirq, peekHiddenSite, skipAmbient,
    getDev, getK, invariant, unsupported, hc, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.TimerDiscipline
