import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEncryption

/-! Actual RX poll and buffered stack callbacks retain the live delayed-effect
carrier. This is a state frame; buffered GRO packet-cause attribution is not
inferred from this preservation theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity TimerSlots Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_store (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv h w.wg) : Inv h v.wg := by
  have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  change v.wg.dev = w.wg.dev at device
  apply hi.retained
  · intro pid timer token found
    simpa only [TimerSlots.view,device] using found
  · simp only [QueuedOccurrences.queue,device]

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved hooks bytes) := by
  unfold Driver.stackObserved
  apply stackReceiveWith_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store
  intro packet
  apply receive4With_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store
  intro dst payload
  exact reply4With_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store _
    (fun family addr packets mtu => product_state (device_transmit family addr packets mtu)) dst payload

theorem stack_flush (packets : List (List UInt8)) : ProductSafe (Driver.stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons packet rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack packet) (fun _ => ih)

theorem candidate_enter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.candidateEnter skb packet) := by
  intro w h hi
  exact ⟨[.scope (.entered ⟨h.length,.candidate skb packet⟩)],rfl,True.intro,hi.append _⟩

theorem candidate_leave (token : Nat) : ProductSafe (hooks.candidateLeave token) := product_emit _

macro "causal_delayed_poll_native" : tactic => `(tactic| (
  apply product_state
  apply state_framed
  · intro initial
    try simp only [getRxSkb,freeRxSkb,WG.andM,branch,endpointFromSkb,invariant,unsupported]
    repeat' first
      | (rx_retention_head PrevQueue.peek; exact retained_store (prevQueuePeek_sameWGStore _) initial)
      | timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Leanux.Proofs.Framing.Preserves (fun w => WorkQueueFrames.view w = initial) _
    try simp only [getRxSkb,freeRxSkb,WG.andM,branch,endpointFromSkb,invariant,unsupported]
    repeat' first
      | (rx_retention_head PrevQueue.peek; exact (WorkQueueFrames.store (prevQueuePeek_sameWGStore _)).wp (fun q => q = initial))
      | send_work_frame_step initial))

theorem receive_poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) :
    ProductSafe (Driver.pollObserved hooks pid budget callback) := by
  unfold Driver.pollObserved CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (causal_delayed_head Driver.Hooks.peerRelease; exact product_state (peer_release _))
    | (causal_delayed_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (causal_delayed_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (causal_delayed_head Driver.Hooks.counterCheck; exact counter _ _)
    | (causal_delayed_head Driver.consumeObserved; exact product_state (consume _ _ _))
    | (causal_delayed_head napiGroReceivePrefix; exact napiGroReceivePrefix_preserves callback
        (fun _ _ _ => True.intro) safe _ _)
    | (causal_delayed_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_preserves callback
        (fun _ _ _ => True.intro) safe _)
    | (causal_delayed_head liftWGPrefix; solve | causal_delayed_poll_native)
    | causal_delayed_product_step

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (Driver.nativePollObserved hooks pid budget) := by
  have callback := GroOccurrence.stack_preserves (fun h w => Inv h w.wg) (fun _ => True)
    (fun _ _ _ => True.intro) hooks.stackInput (Driver.stackObserved hooks) stack
    (fun entry _ safe => product_scope (.stackInput entry) _ (fun _ => safe))
  unfold Driver.nativePollObserved RetirementSecurity.NestedPeerRelease.pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (causal_delayed_head Driver.Hooks.peerRelease; exact product_state (peer_release _))
    | (causal_delayed_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (causal_delayed_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (causal_delayed_head Driver.Hooks.counterCheck; exact counter _ _)
    | (causal_delayed_head Driver.consumeObserved; exact product_state (consume _ _ _))
    | (causal_delayed_head GroOccurrence.receiveWith; exact GroOccurrence.receive_preserves
        (fun h w => Inv h w.wg) (fun _ => True) (fun _ _ _ => True.intro) _ callback _ _)
    | (causal_delayed_head GroOccurrence.flushAllWith; exact GroOccurrence.flushAll_preserves
        (fun h w => Inv h w.wg) (fun _ => True) (fun _ _ _ => True.intro) _ callback _)
    | (causal_delayed_head liftWGPrefix; solve | causal_delayed_poll_native)
    | causal_delayed_product_step

private theorem pending : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) := by
  apply product_state
  unfold RxNapi.pendingSource
  causal_delayed_native

private theorem scheduled : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) := by
  apply product_state
  unfold RxNapi.scheduledSource
  causal_delayed_native

theorem softirq : ProductSafe (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store pending native_poll

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store pending native_poll

theorem irq_exit : ProductSafe (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := fun h w => Inv h w.wg) (fun _ _ _ => True.intro) product_store scheduled softirq

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
