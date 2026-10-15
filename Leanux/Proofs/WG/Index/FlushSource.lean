import Leanux.Proofs.WG.Index.FlushFrames
import Leanux.Proofs.WG.Index.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem runFlushedSendWork_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ runFlushedSendWork pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hq := modifySendWorkQueue_tables (fun queue => queue.erase pid)
  have hp := setPeer_tables
  have hh := hidden_kernel_spec TablesSafeKernel
  have hb := (ensures_iff _ _ _).mp (handshakeSendWorker_tables pid)
  mvcgen [runFlushedSendWork, getPeer, getDev, getK, invariant, hq, hp, hh, hb]

theorem runFlushedClearWork_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ runFlushedClearWork pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hq := modifyClearWorkQueue_tables (fun queue => queue.erase pid)
  have hh := hidden_kernel_spec TablesSafeKernel
  have hb := (ensures_iff _ _ _).mp (queuedExpiredZeroKeyMaterial_tables pid)
  mvcgen [runFlushedClearWork, hq, hh, hb]

/-- The original bounded drain, including named selection, placeholder order,
early return at the requested clear work, and its original stopped outcomes. -/
theorem drainHandshakeSendWq_tables (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hs := runFlushedSendWork_tables
  have hc := runFlushedClearWork_tables
  have hp := TimerDiscipline.peekUnit_spec_kernel_variant TablesSafeKernel
  rw [ensures_iff]
  mvcgen [drainHandshakeSendWq, getDev, getK, resolveUnit, invariant, hs, hc, hp]
  case inv1 => exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

/-- Timer deletion and the actual conditional clear-work flush. -/
theorem timersStop_tables (pid : PeerId) :
    Ensures (timersStop pid) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have ht := delTimer_tables
  have hd := fun upTo => (ensures_iff _ _ _).mp (drainHandshakeSendWq_tables upTo)
  rw [ensures_iff]
  mvcgen [timersStop, getDev, getK, invariant, ht, hd]
  case inv1 => exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

/-- Actual ordered key releases, both flushes, accounting and final peer release.
The deadness guard remains operational; this contract does not assume it succeeds. -/
theorem peerRemoveAfterDead_tables (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hk := keypairsClear_tables
  have ht := (ensures_iff _ _ _).mp (timersStop_tables pid)
  have hd := (ensures_iff _ _ _).mp (drainHandshakeSendWq_tables none)
  have hn := decrementNumPeers_tables
  have hp := peerPut_tables
  rw [ensures_iff]
  mvcgen [peerRemoveAfterDead, getPeer, getDev, getK, branch, invariant,
    unsupported, hk, ht, hd, hn, hp]

end Leanux.Proofs.WG.Index
