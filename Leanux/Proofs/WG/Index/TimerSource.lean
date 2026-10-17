import Leanux.Proofs.WG.Index.CallbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Reuse the exact original selection factor and section wrapper. Every
callback premise is discharged by the concrete all-five family above. -/
theorem fireTimer_tables (worker : Worker) (horizon : UInt64) :
    Ensures (Env.fireTimer worker horizon) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hs := TimerDiscipline.timerSelection_kernel_spec TablesSafeKernel worker horizon
  have hd := delTimer_tables
  have hb := fun pid timer => TimerDiscipline.runTimerSection_kernel_contract worker
    (timerCallback pid timer) TablesSafeKernel TablesSafeKernel
    ((ensures_iff _ _ _).mp (timerCallback_tables pid timer))
  rw [TimerDiscipline.fireTimer_source, ensures_iff]
  mvcgen [TimerDiscipline.fireSelected, hs, hd, hb]

end Leanux.Proofs.WG.Index
