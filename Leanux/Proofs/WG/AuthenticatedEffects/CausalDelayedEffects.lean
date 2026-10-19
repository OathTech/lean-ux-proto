import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedPeerWrite

/-! Live delayed-effect occurrences through the shared arm/queue source. Reads
and peer bookkeeping use native projection frames; only actual arm and append
receipts create new occurrences. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "causal_delayed_timer_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head modPeerTimerGuard; exact guard_retained _ $initial)
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (TimerSlots.Retained $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (TimerSlots.Retained $initial))
  | timer_handshake_step $initial)

macro "causal_delayed_queue_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head peerGet; exact (peerGet_frame _).wp (fun s => s = $initial))
  | (rx_retention_head peerPut; exact (peerPut_frame _).wp (fun s => s = $initial))
  | (rx_retention_head keypairPut; exact (keypairPut_frame _ _).wp (fun s => s = $initial))
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => Queues.WorkQueueFrames.view w = $initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => Queues.WorkQueueFrames.view w = $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => Queues.WorkQueueFrames.view w = $initial))
  | work_queue_step $initial)

macro "causal_delayed_native" : tactic => `(tactic| (
  apply state_framed
  · intro initial
    try simp only [WG.andM,WG.orM,branch,branchCmp,hiddenClock64,peekQueuedUnit,recordQueued,hiddenAlloc,invariant,unsupported]
    repeat' causal_delayed_timer_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Leanux.Proofs.Framing.Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    try simp only [WG.andM,WG.orM,branch,branchCmp,hiddenClock64,peekQueuedUnit,recordQueued,hiddenAlloc,invariant,unsupported]
    repeat' causal_delayed_queue_step initial))

macro "causal_delayed_effect_step" : tactic => `(tactic| first
  | (causal_delayed_read_write_head; first
      | (apply state_read_modify; intro p timer; rfl)
      | (apply state_read_write; · intro p timer; rfl))
  | (causal_delayed_native_head modPeerTimerGuard; exact state_framed _ (guard_retained _) (SendWorkCauses.timer_guard_frame _))
  | (causal_delayed_head TimerEffects.Ops.step; solve | causal_delayed_native)
  | (causal_delayed_head TimerEffects.Ops.arm; exact arm _ _ _ _)
  | (causal_delayed_head TimerEffects.Ops.append; exact queue _)
  | causal_delayed_step)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  repeat' causal_delayed_effect_step

theorem traversal (pid : PeerId) : StateSafe (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | causal_delayed_effect_step

theorem derived (pid : PeerId) : StateSafe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact state_bind (modify_timer _ _ _ _) (fun _ => state_pure _)

theorem data_sent (pid : PeerId) : StateSafe (TimerEffects.dataSentWith effects pid) := by
  unfold TimerEffects.dataSentWith
  repeat' causal_delayed_effect_step

theorem data_received (pid : PeerId) : StateSafe (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | causal_delayed_effect_step

theorem initiated (pid : PeerId) : StateSafe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' causal_delayed_effect_step

theorem queued (pid : PeerId) (retry : Bool) : StateSafe (TimerEffects.queuedWith effects pid retry) := by
  unfold TimerEffects.queuedWith
  repeat' causal_delayed_effect_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
