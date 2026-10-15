import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- An arbitrary peer write leaves the hashed table and allocation cursor unchanged. -/
theorem modifyPeer_tables (pid : PeerId) (f : Peer → Peer) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ Noise.modifyPeer pid f
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  noise_vcgen [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, invariant, hp]

theorem handshakeZero_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ handshakeZero pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [handshakeZero, getPeer, getDev, getK, invariant, hp]

/-- Clear-work queue bookkeeping changes neither table nor cursor. -/
theorem modifyClearWorkQueue_tables (f : List PeerId → List PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄
      modifyDev (fun d => { d with clearWorkQueue := f d.clearWorkQueue })
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases hd : (by assumption : World).k.wg <;>
    simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
