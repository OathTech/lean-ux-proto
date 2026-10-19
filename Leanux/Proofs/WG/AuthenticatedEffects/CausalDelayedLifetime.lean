import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEffects
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptLifetime

/-! The native lifetime observers used inside final-journal TX completion
transport live timer/work occurrences. Newly recorded arms and appends refer
to the same observed callback, including its retained lifetime accesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do TransmitSecurity
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

private theorem framed (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native)
    (timers : ∀ initial, Preserves (TimerSlots.Retained initial) native)
    (work : SameView QueuedOccurrences.queue native) : StateSafe
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  state_observed _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (DelayedEffects.native_retained native timers work)

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (Receipts.lifetime.arm pid timer delay caller) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.arm pid timer delay caller) (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  apply state_current
  intro context
  exact DelayedEffects.observed_arm _ context pid timer delay caller
    (focusStatePrefix_erases _ _ (armTimerPrefix_erases pid timer delay caller))
    (StateAppends.focus _ _ _)

theorem lifetime_queue (pid : PeerId) : StateSafe (Receipts.lifetime.append pid) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  apply state_current
  intro context
  exact DelayedEffects.observed_queue _ context pid
    (focusStatePrefix_erases _ _ (erasesStatePrefix_lift _)) (StateAppends.focus _ _ _)

private theorem step_framed (action : WG.M α)
    (timers : ∀ initial, Preserves (TimerSlots.Retained initial) action)
    (work : SameView QueuedOccurrences.queue action) : StateSafe (Receipts.lifetime.step action) :=
  framed _ action (erasesStatePrefix_lift action) timers work

private theorem peer (pid : PeerId) : StateSafe (Receipts.lifetime.peer pid) := by
  apply framed _ (getPeer pid) (getPeerMixed_erases pid)
  · intro initial
    causal_delayed_timer_step initial
  · exact SendWorkCauses.peer_read_frame pid

private theorem keypair (kid : KeypairId) : StateSafe (Receipts.lifetime.keypair kid) := by
  apply framed _ (getKeypair kid) (getKeypairPrefix_erases kid)
  · intro initial
    causal_delayed_timer_step initial
  · exact SendWorkCauses.key_read_frame kid

private theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (timers : ∀ p timer, ((f p).internalId,(f p).timer timer,(f p).wheel timer) =
      (p.internalId,p.timer timer,p.wheel timer)) : StateSafe (Receipts.lifetime.modifyPeer pid f) := by
  apply framed _ _ (modifyPeerKeysPrefix_erases pid f)
  · intro initial
    apply retained_read initial pid
    intro p known
    apply retained_write initial pid
    intro timer
    rw [timers]
    exact known timer
  · exact (SendWorkCauses.peer_read_frame pid).bind (fun p => SendWorkCauses.peer_write_frame pid (f p))

private theorem guard (pid : PeerId) : StateSafe (Receipts.lifetime.guard pid) :=
  framed _ _ (modPeerTimerGuardPrefix_erases pid) (guard_retained pid)
    (SendWorkCauses.timer_guard_frame pid)

private theorem get (pid : PeerId) : StateSafe (Receipts.lifetime.get pid) :=
  framed _ _ (peerGetMixed_erases pid) (peerGet_retained pid)
    (DelayedEffects.queue_of_frame (peerGet_frame pid))

private theorem put (pid : Option PeerId) : StateSafe (Receipts.lifetime.put pid) :=
  framed _ _ (peerPutMixed_erases pid) (peerPut_retained pid)
    (DelayedEffects.queue_of_frame (peerPut_frame pid))

macro "causal_delayed_lifetime_step" : tactic => `(tactic| first
  | (causal_delayed_head LifetimeEffects.Ops.step
     apply step_framed
     · intro initial
       try simp only [branch,branchCmp,invariant,peekQueuedUnit,recordQueued]
       repeat' causal_delayed_timer_step initial
     · apply DelayedEffects.queue_of_frame
       intro initial
       change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
       try simp only [branch,branchCmp,invariant,peekQueuedUnit,recordQueued]
       repeat' causal_delayed_queue_step initial)
  | (causal_delayed_head LifetimeEffects.Ops.peer; exact peer _)
  | (causal_delayed_head LifetimeEffects.Ops.keypair; exact keypair _)
  | (causal_delayed_head LifetimeEffects.Ops.modifyPeer; apply modify_peer; intro p timer; rfl)
  | (causal_delayed_head LifetimeEffects.Ops.guard; exact guard _)
  | (causal_delayed_head LifetimeEffects.Ops.get; exact get _)
  | (causal_delayed_head LifetimeEffects.Ops.put; exact put _)
  | (causal_delayed_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (causal_delayed_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | causal_delayed_step)

theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (LifetimeEffects.modifyWith Receipts.lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' causal_delayed_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    StateSafe (LifetimeEffects.traversalWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (causal_delayed_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | causal_delayed_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    StateSafe (LifetimeEffects.dataSentWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' causal_delayed_lifetime_step

theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith Receipts.lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' causal_delayed_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (causal_delayed_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | causal_delayed_lifetime_step

private theorem actual_put (peer : Option PeerId) : StateSafe (completionLifetime.put peer) :=
  state_observed _ _ (CallbackFrames.lifetime_put_erases peer)
    (CallbackFrames.lifetime_put_quiet (fun _ : Event => (none : Option Empty))
      (fun _ => rfl) (fun _ => rfl) peer).1
    (DelayedEffects.native_retained _ (peerPut_retained peer)
      (DelayedEffects.queue_of_frame (peerPut_frame peer)))

private theorem actual_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith completionLifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' first
    | (causal_delayed_head LifetimeEffects.Ops.put; exact actual_put _)
    | causal_delayed_lifetime_step

theorem lifetime_actual_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith completionLifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (causal_delayed_head LifetimeEffects.queuedWith; exact actual_queued _ _)
    | (causal_delayed_head LifetimeEffects.Ops.put; exact actual_put _)
    | causal_delayed_lifetime_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
