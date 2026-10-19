import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityCounter
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityStack
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! Actual receive polling and stack callbacks preserve the positional staged
origin carrier, including the history retained on stopped execution prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open AuthenticatedEffects AuthenticatedEffects.CausalJournal TimerSlots Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem candidate_enter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.candidateEnter skb packet) := by
  intro w h hi
  have safe := hi.2.emit (quiet_event (event := .scope (.entered ⟨h.length,.candidate skb packet⟩)) rfl)
  exact ⟨[.scope (.entered ⟨h.length,.candidate skb packet⟩)],rfl,safe,hi.1.append (fun _ _ member => no_use (by simp only [List.mem_singleton] at member; subst_vars; rfl)),safe⟩

theorem candidate_leave (token : Nat) : ProductSafe (hooks.candidateLeave token) := product_emit _ rfl

macro "available_poll_native" : tactic => `(tactic| (
  apply product_state
  apply state_lift
  intro history
  try rw [getPeer_twice]
  try unfold WG.andM
  try simp (config := {zeta := false}) only
    [getRxSkb,freeRxSkb,branch,endpointFromSkb,invariant,unsupported]
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact Native.store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head liftSkb; exact Native.skb _)
    | (allocation_release_lift_from SkbM; exact Native.skb _)
    | (rx_retention_head keypairPut; exact Native.key_put _ _)
    | staged_available_native))

theorem receive_poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) :
    ProductSafe (Driver.pollObserved hooks pid budget callback) := by
  unfold Driver.pollObserved CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (available_origin_product_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (available_origin_product_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (available_origin_product_head Driver.Hooks.counterCheck; exact counter_observed _ _)
    | (available_origin_product_head Driver.consumeObserved; exact product_state (consume_observed _ _ _))
    | (available_origin_product_head napiGroReceivePrefix; exact napiGroReceivePrefix_preserves callback
        (fun _ _ before => before.2) safe _ _)
    | (available_origin_product_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_preserves callback
        (fun _ _ before => before.2) safe _)
    | (available_origin_product_head liftWGPrefix; solve | available_poll_native)
    | available_origin_product_step

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (Driver.nativePollObserved hooks pid budget) := by
  have callback := GroOccurrence.stack_preserves (fun h w => Carrier h w.wg) Safe
    (fun _ _ before => before.2) hooks.stackInput (Driver.stackObserved hooks) stack
    (fun entry _ safe => product_scope (.stackInput entry) _ (fun _ => safe))
  unfold Driver.nativePollObserved GroOccurrencePoll.observed GroOccurrencePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (available_origin_product_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (available_origin_product_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (available_origin_product_head Driver.Hooks.counterCheck; exact counter_observed _ _)
    | (available_origin_product_head Driver.consumeObserved; exact product_state (consume_observed _ _ _))
    | (available_origin_product_head GroOccurrence.receiveWith; exact GroOccurrence.receive_preserves
        (fun h w => Carrier h w.wg) Safe (fun _ _ before => before.2) _ callback _ _)
    | (available_origin_product_head GroOccurrence.flushAllWith; exact GroOccurrence.flushAll_preserves
        (fun h w => Carrier h w.wg) Safe (fun _ _ before => before.2) _ callback _)
    | (available_origin_product_head liftWGPrefix; solve | available_poll_native)
    | available_origin_product_step

private theorem pending : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) := by
  apply product_state
  unfold RxNapi.pendingSource
  apply state_lift
  intro history
  repeat' staged_available_native

private theorem scheduled : ProductSafe (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) := by
  apply product_state
  unfold RxNapi.scheduledSource
  apply state_lift
  intro history
  repeat' staged_available_native

theorem softirq : ProductSafe (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := fun h w => Carrier h w.wg) (fun _ _ before => before.2) product_stable pending native_poll

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := fun h w => Carrier h w.wg) (fun _ _ before => before.2) product_stable pending native_poll

theorem irq_exit : ProductSafe (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := fun h w => Carrier h w.wg) (fun _ _ before => before.2) product_stable scheduled softirq

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
