import Leanux.Proofs.WG.TimerDiscipline.RetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Guarded timer modification does not enqueue a handshake worker. -/
theorem modPeerTimer_sendQueue (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : Option (List PeerId)) :
    ⦃fun w => ⌜w.k.wg.map Device.sendWorkQueue = queue⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ w => ⌜w.k.wg.map Device.sendWorkQueue = queue⌝⦄ := by
  have hh := hidden_kernel_spec (fun k => k.wg.map Device.sendWorkQueue = queue)
  mvcgen [modPeerTimer, callerJiffies, modPeerTimerGuard, Leanux.WG.andM, armTimer,
    hiddenJiffies, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant, unsupported, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

/-- Giving up clears staged packets and timers but does not queue send work. -/
theorem retransmitGiveUp_sendQueue (pid : PeerId) (queue : Option (List PeerId)) :
    ⦃fun w => ⌜w.k.wg.map Device.sendWorkQueue = queue⌝⦄ retransmitGiveUp pid
      ⦃⇓? _ w => ⌜w.k.wg.map Device.sendWorkQueue = queue⌝⦄ := by
  have hm := modPeerTimer_sendQueue .timerJiffiesRetransmitZeroKey pid
    .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS queue
  have hm' := map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  simp only [retransmitGiveUp, Functor.discard, Functor.mapConst]
  mvcgen [delTimer, purgeStagedPackets, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, invariant, hm']
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

  all_goals exact hm' _ (by simp)

end Leanux.Proofs.WG.TimerDiscipline
