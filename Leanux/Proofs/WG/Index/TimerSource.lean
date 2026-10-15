import Leanux.Proofs.WG.Index.TimerFrames
import Leanux.Proofs.WG.Index.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem expiredRetransmitHandshake_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ expiredRetransmitHandshake pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hd := delTimer_tables
  have hp := purgeStagedPackets_tables
  have hc := clearPeerEndpointSrc_tables
  have hs := setPeer_tables
  have hq := sendQueuedHandshakeInitiation_tables
  have hm := fun site timer delay => TimerDiscipline.map_result_spec
    (fun _ : Bool => PUnit.unit) _ _ _ (modPeerTimer_tables site pid timer delay)
  simp only [expiredRetransmitHandshake, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [getPeer, getDev, getK, branch, branchCmp, invariant, hd, hp, hc, hs, hq, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals exact hm _ _ _ _ (by assumption)

theorem expiredSendKeepalive_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ expiredSendKeepalive pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hk := (ensures_iff _ _ _).mp (sendKeepalive_tables pid)
  have hp := setPeer_tables
  have hm := fun site timer delay => TimerDiscipline.map_result_spec
    (fun _ : Bool => PUnit.unit) _ _ _ (modPeerTimer_tables site pid timer delay)
  simp only [expiredSendKeepalive, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [getPeer, getDev, getK, branch, invariant, hk, hp, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals exact hm _ _ _

theorem expiredNewHandshake_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ expiredNewHandshake pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hc := clearPeerEndpointSrc_tables
  have hq := sendQueuedHandshakeInitiation_tables
  mvcgen [expiredNewHandshake, hc, hq]

/-- The already-queued branch retains its actual compensating peer put. -/
theorem expiredZeroKeyMaterial_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ expiredZeroKeyMaterial pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hg := peerGet_tables
  have hp := peerPut_tables
  have hq := Config.recordQueued_kernel TablesSafeKernel
  have hw := modifyClearWorkQueue_tables (fun queue => queue ++ [pid])
  mvcgen [expiredZeroKeyMaterial, getPeer, getDev, getK, branch, invariant, hg, hp, hq, hw]

theorem expiredSendPersistentKeepalive_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ expiredSendPersistentKeepalive pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hk := (ensures_iff _ _ _).mp (sendKeepalive_tables pid)
  mvcgen [expiredSendPersistentKeepalive, getPeer, getDev, getK, branch, invariant, hk]

/-- All five original callbacks, with the actual send/queue/release paths. -/
theorem timerCallback_tables (pid : PeerId) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  rw [ensures_iff]
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_tables pid
  | sendKeepalive => exact expiredSendKeepalive_tables pid
  | newHandshake => exact expiredNewHandshake_tables pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_tables pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_tables pid

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
