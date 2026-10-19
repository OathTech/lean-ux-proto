import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableEffects
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityObservedPeer
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHandshakeAdapters

/-! All native timer callbacks preserve the staged-availability carrier with their
actual keepalive callback. Timer authorization is a separate causal outcome. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem arm_observed (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (effects.arm pid timer delay caller) := by
  apply state_current
  intro context
  exact state_receipt (state_lift _ (fun _ => Native.arm pid timer delay caller)) _ (fun _ => rfl)

theorem queue_observed (pid : PeerId) : StateSafe (effects.append pid) := by
  apply state_current
  intro context
  exact state_receipt (state_lift _ (fun _ => Native.modify_device
    (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) (fun _ => rfl) (fun _ => rfl))) _ (fun _ => rfl)

macro "available_effect_step" : tactic => `(tactic| first
  | (available_effect_update_head; first
      | (apply state_read_modify; intro p; exact ⟨rfl,rfl⟩)
      | (apply state_read_write; · intro p; exact ⟨rfl,rfl⟩))
  | (available_origin_head TimerEffects.Ops.step
     apply state_lift; intro history
     try simp only [peekQueuedUnit,recordQueued]
     repeat' first
       | (rx_retention_head modPeerTimerGuard; exact Native.timer_guard _)
       | staged_available_native
     done)
  | (available_origin_head TimerEffects.Ops.arm; exact arm_observed _ _ _ _)
  | (available_origin_head TimerEffects.Ops.append; exact queue_observed _)
  | available_origin_step)

theorem retransmit (pid : PeerId) : StateSafe (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (available_effect_native_head delTimer; exact state_lift _ (fun _ => Native.delete_timer _ _))
    | (available_effect_native_head purgeStagedPackets; exact state_lift _ (fun _ => Native.purge _))
    | (available_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (available_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | (available_origin_head TimerEffects.queuedWith; exact queued_observed _ _)
    | available_effect_step

theorem expired_keepalive (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.expiredKeepaliveWith effects keepalive pid) := by
  unfold TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | (available_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | available_effect_step

theorem expired_new (pid : PeerId) : StateSafe (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  repeat' first
    | (available_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (available_origin_head TimerEffects.queuedWith; exact queued_observed _ _)
    | available_effect_step

theorem persistent (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.persistentWith effects keepalive pid) := by
  unfold TimerEffects.persistentWith
  repeat' first
    | exact hk _
    | available_effect_step

theorem queued_rich (pid : PeerId) (retry : Bool) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects hooks.peerRelease pid retry) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.queuedWith
  repeat' first
    | (available_origin_head Driver.Hooks.peerRelease; exact peer_release_observed _)
    | available_effect_step

theorem retransmit_rich (pid : PeerId) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.retransmitWith effects hooks.peerRelease hooks.stagedPurge pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (available_origin_head Driver.Hooks.stagedPurge; exact staged_purge_observed _)
    | (available_effect_native_head delTimer; exact state_lift _ (fun _ => Native.delete_timer _ _))
    | (available_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (available_origin_head TimerEffects.modifyWith; exact modify_timer_observed _ _ _ _)
    | (available_origin_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_rich _ _)
    | available_effect_step

theorem expired_new_rich (pid : PeerId) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith effects hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith
  repeat' first
    | (available_effect_native_head clearPeerEndpointSrc; exact state_lift _ (fun _ => Native.clear_endpoint _))
    | (available_origin_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_rich _ _)
    | available_effect_step

theorem timer (pid : PeerId) (kind : PeerTimer) :
    StateSafe (Driver.timerObserved hooks pid kind) := by
  cases kind
  · exact retransmit_rich pid
  · exact expired_keepalive _ keepalive_observed_source pid
  · exact expired_new_rich pid
  · exact state_lift _ (fun _ => Native.expired_zero pid)
  · exact persistent _ keepalive_observed_source pid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
