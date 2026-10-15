import Leanux.Proofs.WG.Index.DispatchFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Original selection, dequeue and section wrapper compose around the checked body. -/
theorem runOneSendWorker_tables : Ensures Env.runOneSendWorker
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hs := sendWorkerSelection_tables
  have hd := sendWorkerDequeue_tables
  have hw := fun pid => TimerDiscipline.runWorker_kernel_contract .sendWorker
    (handshakeSendWorker pid) TablesSafeKernel TablesSafeKernel
    ((ensures_iff _ _ _).mp (handshakeSendWorker_tables pid))
  rw [TimerDiscipline.runOneSendWorker_source, ensures_iff]
  mvcgen [hs, hd, hw]

end Leanux.Proofs.WG.Index
