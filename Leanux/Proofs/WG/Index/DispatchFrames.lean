import Leanux.Proofs.WG.Index.SendFrames
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem sendWorkerSelection_tables :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ TimerDiscipline.sendWorkerSelection
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := TimerDiscipline.peekUnit_dispatch_frame (fun k _ => TablesSafeKernel k)
  mvcgen [TimerDiscipline.sendWorkerSelection, getDev, getK, resolveUnit, invariant, hp]

theorem sendWorkerDequeue_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ TimerDiscipline.sendWorkerDequeue pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [TimerDiscipline.sendWorkerDequeue, getPeer, getDev, getK,
    modifyDev, modifyK, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
