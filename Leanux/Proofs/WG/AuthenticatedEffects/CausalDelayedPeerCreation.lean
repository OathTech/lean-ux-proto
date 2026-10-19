import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedAllowedIps

/-! Creating a peer introduces no pending wheel entry. This uses the pending
timer projection, rather than claiming that a newly resident empty slot was
already resident. Subsequent bookkeeping retains the source getter's fields. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem write_empty_peer (pid : PeerId) (p : Peer) (empty : ∀ t, p.wheel t = none) :
    StateSafe (liftWGPrefix (setPeer pid p)) := by
  apply state_native
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  cases run
  obtain ⟨timers,tickets,work⟩ := hi
  refine ⟨?_,tickets,work.frame ?_⟩
  · intro q t stamp expires entry pending
    cases hd : w.dev with
    | none => simp [Pending,TimerSlots.view,hd] at pending
    | some d =>
      simp only [Pending,TimerSlots.view,hd,Option.map_some,Option.bind_some,
        Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq] at pending
      by_cases same : pid = q
      · simp [same,empty] at pending
      · simp only [ite_eq_right same] at pending
        exact timers q t stamp expires entry (by simpa only [Pending,TimerSlots.view,hd,Option.bind_some] using pending)
  · simp only [QueuedOccurrences.queue,Option.map_map,Function.comp_def]

theorem precompute (pid : PeerId) : StateSafe (liftWGPrefix (precomputeStaticStatic pid)) := by
  apply state_framed
  · intro initial
    unfold precomputeStaticStatic
    simp only [branch,requireNotPending]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold precomputeStaticStatic
    simp only [branch,requireNotPending]
    repeat' send_work_frame_step initial

theorem handshake_init (pid : PeerId) (psk : Option Key) : StateSafe (liftWGPrefix (handshakeInit pid psk)) := by
  apply state_framed
  · intro initial
    unfold handshakeInit IndexOwner.setPeerWord precomputeStaticStatic
    simp only [branch,requireNotPending]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold handshakeInit IndexOwner.setPeerWord precomputeStaticStatic
    simp only [branch,requireNotPending]
    repeat' send_work_frame_step initial

theorem reset_handshake (pid : PeerId) : StateSafe (liftWGPrefix (resetLastSentHandshake pid)) := by
  apply state_framed
  · intro initial
    unfold resetLastSentHandshake hiddenClock64
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold resetLastSentHandshake hiddenClock64
    repeat' send_work_frame_step initial

theorem cache_reset (pid : PeerId) : StateSafe (liftWGPrefix (dstCacheReset pid)) := by
  apply state_framed
  · intro initial
    unfold dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' timer_data_step initial
  · intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' queue_callback_step initial

theorem peer_create (key : Key) (psk : Option Key) : StateSafe (liftWGPrefix (peerCreate key psk)) := by
  apply state_native
  intro h
  unfold peerCreate
  simp only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head setPeer; exact native_contract _ (write_empty_peer _ _ (by intro t; cases t <;> rfl)) h)
    | (rx_retention_head handshakeInit; exact native_contract _ (handshake_init _ _) h)
    | (rx_retention_head resetLastSentHandshake; exact native_contract _ (reset_handshake _) h)
    | (rx_retention_head dstCacheReset; exact native_contract _ (cache_reset _) h)
    | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
