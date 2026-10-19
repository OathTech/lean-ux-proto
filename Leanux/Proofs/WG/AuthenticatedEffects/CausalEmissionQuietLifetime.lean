import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuiet

/-! Native completion lifetime effects preserve existing delivery certificates. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
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
    (fun event => (completion? event).bind CompletionEffects.lifetime?) (fun event => by cases event <;> rfl) body

theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Driver.StateHistorySafe Safe (lifetime.arm pid timer delay caller) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.arm pid timer delay caller)
      (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  exact current_quiet _ (fun _ => receipt_quiet _ (base_safe _) _ (fun _ => rfl))

theorem lifetime_queue (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.append pid) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (base.append pid) (fun r => Event.queued ⟨context,pid,r⟩))
  exact current_quiet _ (fun _ => receipt_quiet _ (base_safe _) _ (fun _ => rfl))

private theorem lifetime_step (action : WG.M α) : Driver.StateHistorySafe Safe (lifetime.step action) := base_safe _
private theorem lifetime_peer (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.peer pid) := base_safe _
private theorem lifetime_key (kid : KeypairId) : Driver.StateHistorySafe Safe (lifetime.keypair kid) := base_safe _
private theorem lifetime_modify (pid : PeerId) (f : Peer → Peer) :
    Driver.StateHistorySafe Safe (lifetime.modifyPeer pid f) := base_safe _
private theorem lifetime_guard (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.guard pid) := base_safe _
private theorem lifetime_get (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.get pid) := base_safe _
private theorem lifetime_put (peer : Option PeerId) : Driver.StateHistorySafe Safe (lifetime.put peer) := base_safe _

macro "emission_delivery_lifetime_step" : tactic => `(tactic| first
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
  repeat' emission_delivery_lifetime_step

theorem lifetime_traversal (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.traversalWith lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head LifetimeEffects.modifyWith; exact lifetime_modify_timer _ _ _ _)
    | emission_delivery_lifetime_step

theorem lifetime_data_sent (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.dataSentWith lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' emission_delivery_lifetime_step

private theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    Driver.StateHistorySafe Safe (LifetimeEffects.queuedWith lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' emission_delivery_lifetime_step

theorem lifetime_fresh (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.freshWith lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (driver_history_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | emission_delivery_lifetime_step

private theorem actual_lifetime_put (peer : Option PeerId) :
    Driver.StateHistorySafe Safe (completionLifetime.put peer) :=
  CallbackHistory.lifetime_put
    (fun body => quiet_state
      (HandshakeSecurity.StagedDisposal.LifetimeSource.peerEncode (Event.old ∘ Journal.completionEvent))
      (HandshakeSecurity.StagedDisposal.LifetimeSource.peerDecode completion?)
      (fun _ => rfl) body)
    (fun event => emit_quiet (.stagedDisposal event) rfl) peer

private theorem actual_lifetime_queued (pid : PeerId) (retry : Bool) :
    Driver.StateHistorySafe Safe (LifetimeEffects.queuedWith completionLifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' first
    | (driver_history_head LifetimeEffects.Ops.put; exact actual_lifetime_put _)
    | emission_delivery_lifetime_step

theorem lifetime_actual_fresh (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.freshWith completionLifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (driver_history_head LifetimeEffects.queuedWith; exact actual_lifetime_queued _ _)
    | (driver_history_head LifetimeEffects.Ops.put; exact actual_lifetime_put _)
    | emission_delivery_lifetime_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
