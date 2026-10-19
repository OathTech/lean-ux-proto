import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedProduct

/-! Native non-effect leaves of TX completion retain live timer/work
occurrences. Socket routing/cache updates and object repayments use their
actual projection frames, not an assumed quiet transmitter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem holder_queue (native : WG.M α)
    (frame : ∀ initial, Preserves (Queues.RxCredits.DurableHolders.Frame initial) native) :
    SameView QueuedOccurrences.queue native := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  have output := (hoare_iff_run_ambient _ _ _).mp (frame w) w a value v b
    (Queues.RxCredits.DurableHolders.Frame.refl w) run
  exact congrArg (fun q => q.getD []) output.send

theorem socket4 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    StateSafe (liftWGPrefix (send4 e cache bytes ds exactRx)) :=
  state_framed _
    ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerSocketFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots.send4_frame) e cache bytes ds exactRx)
    (holder_queue _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e cache bytes ds exactRx))

theorem socket6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    StateSafe (liftWGPrefix (send6 e cache bytes ds exactRx)) :=
  state_framed _
    ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerSocketFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots.send6_frame) e cache bytes ds exactRx)
    (holder_queue _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e cache bytes ds exactRx))

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    StateSafe (liftWGPrefix (sendSkbToPeer pid bytes ds)) := by
  apply state_framed
  · intro initial
    unfold sendSkbToPeer
    simp only [branch]
    repeat' first
      | (rx_retention_head send4; exact (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerSocketFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots.send4_frame) _ _ _ _ _ initial)
      | (rx_retention_head send6; exact (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerSocketFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots.send6_frame) _ _ _ _ _ initial)
      | timer_handshake_step initial
  · intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold sendSkbToPeer
    simp only [branch]
    repeat' first
      | (rx_retention_head send4
         exact (holder_queue _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) _ _ _ _ _)).wp (fun q => q = initial))
      | (rx_retention_head send6
         exact (holder_queue _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) _ _ _ _ _)).wp (fun q => q = initial))
      | queue_callback_step initial

theorem skb (native : SkbM α) : StateSafe (liftWGPrefix (liftSkb native)) :=
  state_framed _ (skb_retained native) (SendWorkCauses.skb_frame native)

theorem drop_completion (pid : PeerId) : StateSafe
    (liftWGPrefix (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked})) := by
  causal_delayed_native

theorem dispose_completion (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    StateSafe (liftWGPrefix (Queues.TxDisposition.disposeSource pid items key)) := by
  apply state_framed
  · intro initial
    unfold Queues.TxDisposition.disposeSource freeTxSkb
    repeat' first
      | (rx_retention_head liftSkb; exact skb_retained _ initial)
      | causal_delayed_timer_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold Queues.TxDisposition.disposeSource freeTxSkb
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (fun w => Queues.WorkQueueFrames.view w = initial)
         intro id state
         change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _)
      | (rx_retention_head liftSkb
         apply hoare_liftSkb
         intro w d store hi hd
         simpa only [Queues.WorkQueueFrames.view,hd,Option.map_some] using hi)
      | causal_delayed_queue_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
