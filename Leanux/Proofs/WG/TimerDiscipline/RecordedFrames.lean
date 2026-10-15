import Leanux.Proofs.WG.TimerDiscipline.ArmingSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem hidden_recorded_kernel_spec (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k ∧ w.armRecords = true⌝⦄ hidden site
      ⦃⇓? _ w => ⌜P w.k ∧ w.armRecords = true⌝⦄ := by
  mvcgen [hidden, skipAmbient, noteNetRxStart]

theorem callerJiffies_recorded_spec (site : HiddenSite) (d : Device) :
    ⦃fun w => ⌜w.k.wg = some d ∧ w.armRecords = true⌝⦄ callerJiffies site
      ⦃⇓? result w => ⌜result.isSome = true ∧ w.k.wg = some d ∧ w.armRecords = true⌝⦄ := by
  have hh := hidden_recorded_kernel_spec (fun k => k.wg = some d) site
  mvcgen [callerJiffies, hiddenJiffies, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all


end Leanux.Proofs.WG.TimerDiscipline
