import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEffects
import Leanux.Proofs.WG.Queues.HolderTimers

/-! All five native timer callbacks transport the same live occurrence
carrier. The callback that clears key material may enqueue clear work; it does
not create a handshake-send ticket or a timer occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem endpoint (pid : PeerId) : StateSafe (effects.step (clearPeerEndpointSrc pid)) := by
  apply state_framed
  · intro initial
    unfold clearPeerEndpointSrc dstCacheResetNow
    repeat' first
      | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
      | timer_handshake_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' first
      | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
      | work_queue_step initial

private theorem purge (pid : PeerId) : StateSafe (effects.step (purgeStagedPackets pid)) := by
  apply state_framed
  · intro initial
    unfold purgeStagedPackets
    repeat' timer_handshake_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold purgeStagedPackets
    repeat' work_queue_step initial

theorem expired_zero (pid : PeerId) : StateSafe (effects.step (expiredZeroKeyMaterial pid)) := by
  apply state_framed
  · intro initial
    unfold expiredZeroKeyMaterial
    simp only [branch,peekQueuedUnit,recordQueued]
    repeat' timer_handshake_step initial
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    have frame := (hoare_iff_run_ambient _ _ _).mp
      (Queues.RxCredits.HolderTimers.expiredZero_frame pid w) w a value v b
      (Queues.RxCredits.HolderTimers.ClearFrame.refl w) run
    exact congrArg (fun q => q.getD []) frame.send

theorem retransmit (pid : PeerId) : StateSafe (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_native_head delTimer; exact delete _ _)
    | (causal_delayed_native_head purgeStagedPackets; exact purge _)
    | (causal_delayed_native_head clearPeerEndpointSrc; exact endpoint _)
    | (causal_delayed_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | (causal_delayed_head TimerEffects.queuedWith; exact queued _ _)
    | causal_delayed_effect_step

theorem expired_keepalive (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.expiredKeepaliveWith effects keepalive pid) := by
  unfold TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | (causal_delayed_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | causal_delayed_effect_step

theorem expired_new (pid : PeerId) : StateSafe (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  repeat' first
    | (causal_delayed_native_head clearPeerEndpointSrc; exact endpoint _)
    | (causal_delayed_head TimerEffects.queuedWith; exact queued _ _)
    | causal_delayed_effect_step

theorem persistent (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.persistentWith effects keepalive pid) := by
  unfold TimerEffects.persistentWith
  repeat' first
    | exact hk _
    | causal_delayed_effect_step

theorem timer (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) (kind : PeerTimer) :
    StateSafe (TimerEffects.timerWith effects keepalive pid kind) := by
  cases kind
  · exact retransmit pid
  · exact expired_keepalive keepalive hk pid
  · exact expired_new pid
  · exact expired_zero pid
  · exact persistent keepalive hk pid

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
