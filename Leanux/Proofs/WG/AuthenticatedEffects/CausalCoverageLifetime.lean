import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! Completion's native lifetime callbacks retain coverage under an existing
completion scope, including their old lifetime receipts and later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev base := CompletionEffects.lifetimeBase
  (Event.old ∘ Journal.completionEvent) completion?

def lifetime := LifetimeEffects.decorate base scope? Event.armed Event.queued

private theorem base_safe (body : MixedM α) : StateAt frames
    (focusStatePrefix ((Event.old ∘ Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event => (completion? event).bind CompletionEffects.lifetime?) body) :=
  state_focus _ _ (fun event => by cases event <;> rfl)
    (fun event impossible => by cases event <;> exact impossible.elim) body

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (live : frames ≠ []) : StateAt frames (lifetime.arm pid timer delay caller) := by
  change StateAt frames (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.arm pid timer delay caller)
      (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  exact state_current _ (fun _ => state_receipt _ (base_safe _) _ (fun _ => rfl) (fun _ _ => live))

theorem lifetime_queue (pid : PeerId) (live : frames ≠ []) : StateAt frames (lifetime.append pid) := by
  change StateAt frames (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  exact state_current _ (fun _ => state_receipt _ (base_safe _) _ (fun _ => rfl) (fun _ _ => live))

private theorem lifetime_step (action : WG.M α) : StateAt frames (lifetime.step action) := base_safe _
private theorem lifetime_peer (pid : PeerId) : StateAt frames (lifetime.peer pid) := base_safe _
private theorem lifetime_key (kid : KeypairId) : StateAt frames (lifetime.keypair kid) := base_safe _
private theorem lifetime_modify (pid : PeerId) (f : Peer → Peer) :
    StateAt frames (lifetime.modifyPeer pid f) := base_safe _
private theorem lifetime_guard (pid : PeerId) : StateAt frames (lifetime.guard pid) := base_safe _
private theorem lifetime_get (pid : PeerId) : StateAt frames (lifetime.get pid) := base_safe _
private theorem lifetime_put (peer : Option PeerId) : StateAt frames (lifetime.put peer) := base_safe _

macro "coverage_lifetime_step" live:ident : tactic => `(tactic| first
  | (coverage_head LifetimeEffects.Ops.step; exact lifetime_step _)
  | (coverage_head LifetimeEffects.Ops.peer; exact lifetime_peer _)
  | (coverage_head LifetimeEffects.Ops.keypair; exact lifetime_key _)
  | (coverage_head LifetimeEffects.Ops.modifyPeer; exact lifetime_modify _ _)
  | (coverage_head LifetimeEffects.Ops.guard; exact lifetime_guard _)
  | (coverage_head LifetimeEffects.Ops.get; exact lifetime_get _)
  | (coverage_head LifetimeEffects.Ops.put; exact lifetime_put _)
  | (coverage_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _ $live)
  | (coverage_head LifetimeEffects.Ops.append; exact lifetime_queue _ $live)
  | coverage_state_step)

private theorem lifetime_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (live : frames ≠ []) : StateAt frames (LifetimeEffects.modifyWith lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' coverage_lifetime_step live

theorem lifetime_traversal (pid : PeerId) (live : frames ≠ []) :
    StateAt frames (LifetimeEffects.traversalWith lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _ live)
    | coverage_lifetime_step live

theorem lifetime_data_sent (pid : PeerId) (live : frames ≠ []) :
    StateAt frames (LifetimeEffects.dataSentWith lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' coverage_lifetime_step live

private theorem lifetime_queued (pid : PeerId) (retry : Bool) (live : frames ≠ []) :
    StateAt frames (LifetimeEffects.queuedWith lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' coverage_lifetime_step live

theorem lifetime_fresh (pid : PeerId) (live : frames ≠ []) :
    StateAt frames (LifetimeEffects.freshWith lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (coverage_head LifetimeEffects.queuedWith; exact lifetime_queued _ _ live)
    | coverage_lifetime_step live

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
