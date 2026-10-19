import Leanux.Proofs.WG.AuthenticatedEffects.CausalDisposalScopeFrames
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

private theorem queued_disposal (pid : PeerId) (retry : Bool) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects hooks.peerRelease pid retry) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.queuedWith
  repeat' first
    | (scope_balance_head Driver.Hooks.peerRelease; exact peer_release _)
    | scope_effect_step

private theorem retransmit_disposal (pid : PeerId) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.retransmitWith effects hooks.peerRelease hooks.stagedPurge pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head Driver.Hooks.stagedPurge; exact staged_purge _)
    | (scope_balance_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | (scope_balance_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_disposal _ _)
    | scope_effect_step

private theorem new_disposal (pid : PeerId) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith effects hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith
  exact state_bind (state_lift _) (fun _=>queued_disposal _ _)

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved hooks pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit_disposal _
  | sendKeepalive => exact expired_keepalive _
  | newHandshake => exact new_disposal _
  | zeroKeyMaterial => exact state_lift _
  | persistentKeepalive => exact persistent _

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
