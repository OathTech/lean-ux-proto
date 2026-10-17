import Leanux.Proofs.WG.Index.TablePeerFrames
import Leanux.Proofs.WG.Index.NewlinkFrames
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem sendBufferToPeer_tables (pid : PeerId) (bytes : List UInt8) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr
    (TimerDiscipline.sendBufferToPeer_spec_send_variant pid bytes
      (TimerDiscipline.sendAt w pid).1 (TimerDiscipline.sendAt w pid).2)
    w result final rfl run
  exact tablesSafe_of_cursor w.k final.k (congrArg Prod.fst h) pre

theorem modPeerTimer_tables (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  mvcgen [modPeerTimer, callerJiffies, hiddenJiffies, modPeerTimerGuard,
    WG.andM, armTimer, getPeer, getDev, getK, branch, invariant, unsupported, hh, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem traversal_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hm := fun site timer delay => modPeerTimer_tables site pid timer delay
  have hd := fun site timer delay => TimerDiscipline.map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ (hm site timer delay)
  simp only [timersTraversal, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [getPeer, getDev, getK, branchCmp, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals exact hd _ _ _ _ (by assumption)

theorem delKeepalive_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [timersAnyAuthenticatedPacketSent, delTimer, getPeer, getDev, getK, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

theorem timersHandshakeInitiated_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  have hj := TimerDiscipline.jitter_bounded TablesSafeKernel
  have hp := setPeer_tables
  mvcgen [timersHandshakeInitiated, callerJiffies, hiddenJiffies, modPeerTimerGuard,
    WG.andM, armTimer, getPeer, getDev, getK, branch, invariant, unsupported, hh, hj, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

end Leanux.Proofs.WG.Index
