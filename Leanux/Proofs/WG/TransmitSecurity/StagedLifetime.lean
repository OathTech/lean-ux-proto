import Leanux.Proofs.WG.TransmitSecurity.StagedTimerTransport
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptLifetime

/-! Native lifetime observers in TX completion retain exact staged origins
through their actual saved-peer writes, timer arms and work appends. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do TransmitSecurity
open AuthenticatedEffects AuthenticatedEffects.CausalJournal Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

private theorem framed (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native)
    (kept : ∀ h, Preserves (Inv h) native) : StateSafe
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ selection? (fun _ => rfl) (body.run w))
    (focusStatePrefix_erases _ _ erases) kept

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (Receipts.lifetime.arm pid timer delay caller) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.arm pid timer delay caller) (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  apply state_current
  intro context
  exact state_receipt (framed _ _ (armTimerPrefix_erases pid timer delay caller)
    (fun _ => Native.arm pid timer delay caller)) _ (fun _ => True.intro)

theorem lifetime_queue (pid : PeerId) : StateSafe (Receipts.lifetime.append pid) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context => receiptWGObserved
    (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  apply state_current
  intro context
  exact state_receipt (framed _ _ (erasesStatePrefix_lift _)
    (fun _ => Native.modify_device (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
      (fun _ => rfl) (fun _ => rfl))) _ (fun _ => True.intro)

private theorem step_framed (action : WG.M α)
    (kept : ∀ h, Preserves (Inv h) action) : StateSafe (Receipts.lifetime.step action) :=
  framed _ action (erasesStatePrefix_lift action) kept

private theorem peer (pid : PeerId) : StateSafe (Receipts.lifetime.peer pid) :=
  framed _ _ (getPeerMixed_erases pid) (fun _ => Native.read_peer pid)

private theorem keypair (kid : KeypairId) : StateSafe (Receipts.lifetime.keypair kid) :=
  framed _ _ (getKeypairPrefix_erases kid) (fun _ => Native.read_key kid)

private theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    StateSafe (Receipts.lifetime.modifyPeer pid f) :=
  framed _ _ (modifyPeerKeysPrefix_erases pid f) (fun _ => Native.update_peer pid f same)

private theorem guard (pid : PeerId) : StateSafe (Receipts.lifetime.guard pid) :=
  framed _ _ (modPeerTimerGuardPrefix_erases pid) (fun _ => Native.timer_guard pid)

private theorem get (pid : PeerId) : StateSafe (Receipts.lifetime.get pid) :=
  framed _ _ (peerGetMixed_erases pid) (fun _ => Native.peer_get pid)

private theorem put (pid : Option PeerId) : StateSafe (Receipts.lifetime.put pid) :=
  framed _ _ (peerPutMixed_erases pid) (fun _ => Native.peer_put pid)

macro "staged_lifetime_step" : tactic => `(tactic| first
  | (staged_origin_head LifetimeEffects.Ops.step
     apply step_framed
     intro history
     try simp only [branch,branchCmp,invariant,peekQueuedUnit,recordQueued]
     repeat' first
       | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp _)
       | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp _)
       | staged_origin_native)
  | (staged_origin_head LifetimeEffects.Ops.peer; exact peer _)
  | (staged_origin_head LifetimeEffects.Ops.keypair; exact keypair _)
  | (staged_origin_head LifetimeEffects.Ops.modifyPeer; apply modify_peer; intro p; exact ⟨rfl,rfl⟩)
  | (staged_origin_head LifetimeEffects.Ops.guard; exact guard _)
  | (staged_origin_head LifetimeEffects.Ops.get; exact get _)
  | (staged_origin_head LifetimeEffects.Ops.put; exact put _)
  | (staged_origin_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (staged_origin_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | staged_origin_step)

theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (LifetimeEffects.modifyWith Receipts.lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' staged_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    StateSafe (LifetimeEffects.traversalWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (staged_origin_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | staged_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    StateSafe (LifetimeEffects.dataSentWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' staged_lifetime_step

theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith Receipts.lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' staged_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith Receipts.lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (staged_origin_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | staged_lifetime_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
