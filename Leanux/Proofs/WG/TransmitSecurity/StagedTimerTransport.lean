import Leanux.Proofs.WG.TransmitSecurity.StagedTimerCallbackFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObservedPeerUpdate
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeAdapters
import Leanux.Proofs.WG.TransmitSecurity.StagedRichSourceOrigins

/-! All native timer callbacks preserve the staged-origin carrier with their
actual keepalive callback. Timer authorization is a separate causal outcome. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem disposal_purge_observed (pid : PeerId) : StateSafe (stagedPurge pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.purge_erases pid))
    (fun _ => Native.purge pid)

theorem arm_observed (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (effects.arm pid timer delay caller) := by
  apply state_current
  intro context
  exact state_receipt (state_lift _ (fun _ => Native.arm pid timer delay caller)) _ (fun _ => True.intro)

theorem queue_observed (pid : PeerId) : StateSafe (effects.append pid) := by
  apply state_current
  intro context
  exact state_receipt (state_lift _ (fun _ => Native.modify_device
    (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) (fun _ => rfl) (fun _ => rfl))) _ (fun _ => True.intro)

macro "staged_effect_step" : tactic => `(tactic| first
  | (staged_effect_update_head; first
      | (apply state_read_modify; intro p; exact ⟨rfl,rfl⟩)
      | (apply state_read_write; · intro p; exact ⟨rfl,rfl⟩))
  | (staged_origin_head TimerEffects.Ops.step
     apply state_lift; intro history
     try simp only [peekQueuedUnit,recordQueued]
     repeat' first
       | (rx_retention_head modPeerTimerGuard; exact Native.timer_guard _)
       | staged_origin_native
     done)
  | (staged_origin_head TimerEffects.Ops.arm; exact arm_observed _ _ _ _)
  | (staged_origin_head TimerEffects.Ops.append; exact queue_observed _)
  | staged_origin_step)

theorem retransmit (pid : PeerId) : StateSafe (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (staged_effect_native_head delTimer; exact state_lift _ (fun _ => Native.delete_timer _ _))
    | (staged_effect_native_head purgeStagedPackets; exact state_lift _ (fun _ => Native.purge _))
    | (staged_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (staged_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | (staged_origin_head TimerEffects.queuedWith; exact queued_observed _ _)
    | staged_effect_step

theorem expired_keepalive (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.expiredKeepaliveWith effects keepalive pid) := by
  unfold TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | (staged_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | staged_effect_step

theorem expired_new (pid : PeerId) : StateSafe (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  repeat' first
    | (staged_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (staged_origin_head TimerEffects.queuedWith; exact queued_observed _ _)
    | staged_effect_step

theorem persistent (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.persistentWith effects keepalive pid) := by
  unfold TimerEffects.persistentWith
  repeat' first
    | exact hk _
    | staged_effect_step

theorem timer (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) (kind : PeerTimer) :
    StateSafe (TimerEffects.timerWith effects keepalive pid kind) := by
  cases kind
  · exact retransmit pid
  · exact expired_keepalive keepalive hk pid
  · exact expired_new pid
  · exact state_lift _ (fun _ => Native.expired_zero pid)
  · exact persistent keepalive hk pid


theorem queued_rich (pid : PeerId) (retry : Bool) : StateSafe
    (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.queuedWith
  repeat' first
    | (staged_origin_head peerRelease; exact disposal_release_observed _)
    | staged_effect_step

theorem retransmit_rich (pid : PeerId) : StateSafe
    (HandshakeSecurity.StagedDisposal.Effects.retransmitWith effects peerRelease stagedPurge pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (staged_origin_head stagedPurge; exact disposal_purge_observed _)
    | (staged_effect_native_head delTimer; exact state_lift _ (fun _ => Native.delete_timer _ _))
    | (staged_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (staged_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | (staged_origin_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_rich _ _)
    | staged_effect_step

theorem expired_new_rich (pid : PeerId) : StateSafe
    (HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith effects peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith
  repeat' first
    | (staged_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (staged_origin_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_rich _ _)
    | staged_effect_step

theorem timer_rich (pid : PeerId) (kind : PeerTimer) : StateSafe (Driver.timerObserved hooks pid kind) := by
  cases kind
  · exact retransmit_rich pid
  · exact expired_keepalive _ keepalive_observed_source pid
  · exact expired_new_rich pid
  · exact state_lift _ (fun _ => Native.expired_zero pid)
  · exact persistent _ keepalive_observed_source pid


end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
