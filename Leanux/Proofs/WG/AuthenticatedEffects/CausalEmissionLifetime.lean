import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptLifetime

/-! Actual lifetime-observed completion timer/work callbacks preserve ordered
emission accounting. Their own access, arm and queue events are retained and
are quiet only in the independent datagram-append projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

private theorem framed (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) : StateSafe
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  state_observed _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (focus_state_quiet _ _ (fun _ => rfl) _) frame

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (Receipts.lifetime.arm pid timer delay caller) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.arm pid timer delay caller) (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  apply state_current
  intro context
  apply state_receipt
  · exact framed _ _ (armTimerPrefix_erases pid timer delay caller) (EmissionFrames.arm pid timer delay caller)
  · intro _; rfl

theorem lifetime_queue (pid : PeerId) : StateSafe (Receipts.lifetime.append pid) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  apply state_current
  intro context
  apply state_receipt
  · exact framed _ _ (erasesStatePrefix_lift _) (by sent_frame [] using [])
  · intro _; rfl

private theorem step_framed (action : WG.M α) (frame : SameView WGWorld.sent action) :
    StateSafe (Receipts.lifetime.step action) := framed _ action (erasesStatePrefix_lift action) frame
private theorem peer (pid : PeerId) : StateSafe (Receipts.lifetime.peer pid) :=
  framed _ _ (getPeerMixed_erases pid) (by sent_frame [] using [getPeer_sent_spec])
private theorem keypair (kid : KeypairId) : StateSafe (Receipts.lifetime.keypair kid) :=
  framed _ _ (getKeypairPrefix_erases kid) (by sent_frame [] using [getKeypair_sent_spec])
private theorem modify_peer (pid : PeerId) (f : Peer → Peer) : StateSafe (Receipts.lifetime.modifyPeer pid f) :=
  framed _ _ (modifyPeerKeysPrefix_erases pid f)
    (by sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec])
private theorem guard (pid : PeerId) : StateSafe (Receipts.lifetime.guard pid) :=
  framed _ _ (modPeerTimerGuardPrefix_erases pid) (EmissionFrames.guard pid)
private theorem get (pid : PeerId) : StateSafe (Receipts.lifetime.get pid) :=
  framed _ _ (peerGetMixed_erases pid) (peerGet_sent pid)
private theorem put (pid : Option PeerId) : StateSafe (Receipts.lifetime.put pid) :=
  framed _ _ (peerPutMixed_erases pid) (peerPut_sent pid)

macro "emission_lifetime_step" : tactic => `(tactic| first
  | (emission_head LifetimeEffects.Ops.step
     apply step_framed
     first
     | (emission_frame_head callerJiffies; exact (callerJiffies_sameWGWorld _).factor WGWorld.sent)
     | (emission_frame_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).factor WGWorld.sent)
     | (emission_frame_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).factor WGWorld.sent)
     | (emission_frame_head peekQueuedUnit; sent_frame [peekQueuedUnit] using [])
     | (emission_frame_head recordQueued; sent_frame [recordQueued] using [])
     | sent_frame [] using [])
  | (emission_head LifetimeEffects.Ops.peer; exact peer _)
  | (emission_head LifetimeEffects.Ops.keypair; exact keypair _)
  | (emission_head LifetimeEffects.Ops.modifyPeer; exact modify_peer _ _)
  | (emission_head LifetimeEffects.Ops.guard; exact guard _)
  | (emission_head LifetimeEffects.Ops.get; exact get _)
  | (emission_head LifetimeEffects.Ops.put; exact put _)
  | (emission_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (emission_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | emission_step)

theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (LifetimeEffects.modifyWith Receipts.lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' emission_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    StateSafe (LifetimeEffects.traversalWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | emission_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    StateSafe (LifetimeEffects.dataSentWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' emission_lifetime_step

theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith Receipts.lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' emission_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (emission_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | emission_lifetime_step


private theorem actual_put (peer : Option PeerId) : StateSafe (completionLifetime.put peer) :=
  state_callback _ (CallbackFrames.lifetime_put_quiet contributing? (fun _ => rfl) (fun _ => rfl) peer)
    (CallbackFrames.lifetime_put_erases peer) (peerPut_sent peer)

private theorem actual_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith completionLifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' first
    | (emission_head LifetimeEffects.Ops.put; exact actual_put _)
    | emission_lifetime_step

theorem lifetime_actual_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith completionLifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (emission_head LifetimeEffects.queuedWith; exact actual_queued _ _)
    | (emission_head LifetimeEffects.Ops.put; exact actual_put _)
    | emission_lifetime_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
