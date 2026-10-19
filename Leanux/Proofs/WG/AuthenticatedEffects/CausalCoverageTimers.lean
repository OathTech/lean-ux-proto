import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! Native timer callbacks require the selected timer scope established by the
real dispatcher. This file does not assume arbitrary timer invocations carry a
causal parent. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000

theorem retransmit (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head TimerEffects.modifyWith; exact modify_timer _ _ _ _ live)
    | (coverage_head TimerEffects.queuedWith; exact queued _ _ live)
    | coverage_effect_step live

theorem expired_keepalive (pid : PeerId) (live : frames ≠ []) : StateAt frames (Driver.expiredKeepaliveObserved hooks pid) := by
  unfold Driver.expiredKeepaliveObserved TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head Driver.keepaliveObserved; exact keepalive _ live)
    | (coverage_head TimerEffects.modifyWith; exact modify_timer _ _ _ _ live)
    | coverage_effect_step live

theorem expired_new (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  exact state_bind (state_lift _) (fun _ => queued _ _ live)

theorem persistent (pid : PeerId) (live : frames ≠ []) : StateAt frames (Driver.persistentObserved hooks pid) := by
  unfold Driver.persistentObserved TimerEffects.persistentWith
  repeat' first
    | (coverage_head Driver.keepaliveObserved; exact keepalive _ live)
    | coverage_effect_step live

theorem timer_callback (pid : PeerId) (timer : PeerTimer) (live : frames ≠ []) :
    StateAt frames (Driver.timerObserved hooks pid timer) := by
  cases timer
  · exact retransmit pid live
  · exact expired_keepalive pid live
  · exact expired_new pid live
  · exact state_lift _
  · exact persistent pid live

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
