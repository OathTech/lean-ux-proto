import Leanux.Proofs.WG.Index.TimerFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Send-work queue bookkeeping changes neither table nor allocation cursor. -/
theorem modifySendWorkQueue_tables (f : List PeerId → List PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄
      modifyDev (fun d => { d with sendWorkQueue := f d.sendWorkQueue })
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases hd : (by assumption : World).k.wg <;>
    simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

/-- Peer-count accounting leaves the table and allocation cursor unchanged. -/
theorem decrementNumPeers_tables :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄
      modifyDev (fun d => { d with numPeers := d.numPeers - 1 })
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases hd : (by assumption : World).k.wg <;>
    simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
