import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeStaging

/-! Every actual timer callback restores the incoming lexical scope stack;
the selected wheel occurrence and its arm provenance are separate witnesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000

theorem retransmit (pid : PeerId) : StateSafe (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | (scope_balance_head TimerEffects.queuedWith; exact queued _ _)
    | scope_effect_step

theorem expired_keepalive (pid : PeerId) : StateSafe (Driver.expiredKeepaliveObserved hooks pid) := by
  unfold Driver.expiredKeepaliveObserved TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head Driver.keepaliveObserved; exact keepalive _)
    | (scope_balance_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | scope_effect_step

theorem expired_new (pid : PeerId) : StateSafe (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  exact state_bind (state_lift _) (fun _ => queued _ _)

theorem persistent (pid : PeerId) : StateSafe (Driver.persistentObserved hooks pid) := by
  unfold Driver.persistentObserved TimerEffects.persistentWith
  repeat' first
    | (scope_balance_head Driver.keepaliveObserved; exact keepalive _)
    | scope_effect_step

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved hooks pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit _
  | sendKeepalive => exact expired_keepalive _
  | newHandshake => exact expired_new _
  | zeroKeyMaterial => exact state_lift _
  | persistentKeepalive => exact persistent _

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
