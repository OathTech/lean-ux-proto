import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeEffects

/-! The native lifetime source restores its incoming lexical stack on
normal completion and retains a well-formed stack on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

def lifetime := LifetimeEffects.decorate base scope? Event.armed Event.queued

private theorem base_safe (body : MixedM α) : StateSafe
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  state_focus ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
    (fun event => (completion? event).bind CompletionEffects.lifetime?) (fun event => by cases event <;> rfl) body

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (lifetime.arm pid timer delay caller) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.arm pid timer delay caller)
      (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  exact state_current _ (fun _ => state_receipt _ (base_safe _) _ (fun _ => rfl))

theorem lifetime_queue (pid : PeerId) : StateSafe (lifetime.append pid) := by
  change StateSafe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  exact state_current _ (fun _ => state_receipt _ (base_safe _) _ (fun _ => rfl))

private theorem lifetime_step (action : WG.M α) : StateSafe (lifetime.step action) := base_safe _
private theorem lifetime_peer (pid : PeerId) : StateSafe (lifetime.peer pid) := base_safe _
private theorem lifetime_key (kid : KeypairId) : StateSafe (lifetime.keypair kid) := base_safe _
private theorem lifetime_modify (pid : PeerId) (f : Peer → Peer) :
    StateSafe (lifetime.modifyPeer pid f) := base_safe _
private theorem lifetime_guard (pid : PeerId) : StateSafe (lifetime.guard pid) := base_safe _
private theorem lifetime_get (pid : PeerId) : StateSafe (lifetime.get pid) := base_safe _
private theorem lifetime_put (peer : Option PeerId) : StateSafe (lifetime.put peer) := base_safe _

macro "scope_balanced_lifetime_step" : tactic => `(tactic| first
  | (scope_balance_head LifetimeEffects.Ops.step; exact lifetime_step _)
  | (scope_balance_head LifetimeEffects.Ops.peer; exact lifetime_peer _)
  | (scope_balance_head LifetimeEffects.Ops.keypair; exact lifetime_key _)
  | (scope_balance_head LifetimeEffects.Ops.modifyPeer; exact lifetime_modify _ _)
  | (scope_balance_head LifetimeEffects.Ops.guard; exact lifetime_guard _)
  | (scope_balance_head LifetimeEffects.Ops.get; exact lifetime_get _)
  | (scope_balance_head LifetimeEffects.Ops.put; exact lifetime_put _)
  | (scope_balance_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (scope_balance_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | scope_state_step)

private theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (LifetimeEffects.modifyWith lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' scope_balanced_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    StateSafe (LifetimeEffects.traversalWith lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | scope_balanced_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    StateSafe (LifetimeEffects.dataSentWith lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' scope_balanced_lifetime_step

private theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    StateSafe (LifetimeEffects.queuedWith lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' scope_balanced_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    StateSafe (LifetimeEffects.freshWith lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (scope_balance_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | scope_balanced_lifetime_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
