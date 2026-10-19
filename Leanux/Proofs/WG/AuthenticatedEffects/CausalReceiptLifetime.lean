import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptHistory

/-! The completion path's lifetime observers execute once and retain their
old accesses. Their new timer and queue receipts identify that same native
call and its current lexical context. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

def lifetime := LifetimeEffects.decorate base scope? Event.armed Event.queued

private theorem base_safe (body : MixedM α) : Driver.StateHistorySafe Safe
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  quiet_state ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
    (fun event => (completion? event).bind CompletionEffects.lifetime?) (fun _ => True.intro) body

private theorem base_frame (body : MixedM α) : StateHistoryFrame scope?
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  fun w a h => focusPrefix_other _ _ scope? (fun _ => rfl) (body.run w) a h

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Driver.StateHistorySafe Safe (lifetime.arm pid timer delay caller) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.arm pid timer delay caller)
      (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  exact recorded _ (armTimer pid timer delay caller)
    (focusStatePrefix_erases _ _ (armTimerPrefix_erases pid timer delay caller))
    (base_safe _) (base_frame _) _ (fun _ _ valid => ⟨valid,rfl⟩)

theorem lifetime_queue (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.append pid) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  exact recorded _ (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (focusStatePrefix_erases _ _ (erasesStatePrefix_lift _))
    (base_safe _) (base_frame _) _ (fun _ _ valid => ⟨valid,rfl⟩)

private theorem lifetime_step (action : WG.M α) : Driver.StateHistorySafe Safe (lifetime.step action) := base_safe _
private theorem lifetime_peer (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.peer pid) := base_safe _
private theorem lifetime_key (kid : KeypairId) : Driver.StateHistorySafe Safe (lifetime.keypair kid) := base_safe _
private theorem lifetime_modify (pid : PeerId) (f : Peer → Peer) :
    Driver.StateHistorySafe Safe (lifetime.modifyPeer pid f) := base_safe _
private theorem lifetime_guard (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.guard pid) := base_safe _
private theorem lifetime_get (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.get pid) := base_safe _
private theorem lifetime_put (peer : Option PeerId) : Driver.StateHistorySafe Safe (lifetime.put peer) := base_safe _

macro "receipt_lifetime_step" : tactic => `(tactic| first
  | (driver_history_head LifetimeEffects.Ops.step; exact lifetime_step _)
  | (driver_history_head LifetimeEffects.Ops.peer; exact lifetime_peer _)
  | (driver_history_head LifetimeEffects.Ops.keypair; exact lifetime_key _)
  | (driver_history_head LifetimeEffects.Ops.modifyPeer; exact lifetime_modify _ _)
  | (driver_history_head LifetimeEffects.Ops.guard; exact lifetime_guard _)
  | (driver_history_head LifetimeEffects.Ops.get; exact lifetime_get _)
  | (driver_history_head LifetimeEffects.Ops.put; exact lifetime_put _)
  | (driver_history_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (driver_history_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | driver_state_history_step)

private theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Driver.StateHistorySafe Safe (LifetimeEffects.modifyWith lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' receipt_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.traversalWith lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | receipt_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.dataSentWith lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' receipt_lifetime_step

private theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    Driver.StateHistorySafe Safe (LifetimeEffects.queuedWith lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' receipt_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.freshWith lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (driver_history_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | receipt_lifetime_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
