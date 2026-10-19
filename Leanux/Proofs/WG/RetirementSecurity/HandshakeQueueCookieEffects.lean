import Leanux.Proofs.WG.TransmitSecurity.CookieInputHandshake
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalOuter

/-! Actual send and completion callbacks append no cookie-input obligation.
They retain the same existing history while recording their native effects. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects
open CausalJournal CookieInput HandshakeSecurity Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem initiated (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' effect_history_step effects_safe

private theorem send_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
        (ProtocolSender.sendOps Event.protocolSocket scope?))) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (driver_history_head StagedDisposal.Decoration.release; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _=>True.intro) _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head receiptWGObserved; exact receipt_quiet _ (Driver.History.state_lift _) _ (fun _=>True.intro))
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | (driver_history_head TimerEffects.initiatedWith; exact initiated _)
    | driver_state_history_step

private theorem flushed_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange
        (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
          (ProtocolSender.sendOps Event.protocolSocket scope?))) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (driver_history_head SendExchange.workerWith; exact send_body _)
    | driver_state_history_step

theorem flushed_send (pid : PeerId) : Driver.StateHistorySafe Safe (flushedSend pid) := by
  intro w a h hi
  exact state_scope (.sendWork pid (CausalSources.sendEntry pid w)) _ (flushed_body pid) w a h hi

theorem send_worker : Driver.ProductHistorySafe Safe (Driver.sendWorkerObserved CausalJournal.hooks) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  exact Driver.History.product_bind (Driver.History.product_lift _) (fun pid=>
    Driver.History.product_state (flushed_send pid))

private abbrev base := CompletionEffects.lifetimeBase (Event.old ∘ TransmitSecurity.Journal.completionEvent) completion?
private abbrev lifetime := LifetimeEffects.decorate base scope? Event.armed Event.queued

private theorem base_safe (body : MixedM α) : Driver.StateHistorySafe Safe
    (focusStatePrefix ((Event.old ∘ TransmitSecurity.Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
      (fun event=>(completion? event).bind CompletionEffects.lifetime?) body) :=
  quiet_state ((Event.old ∘ TransmitSecurity.Journal.completionEvent) ∘ CompletionEffects.lifetimeEvent)
    (fun event=>(completion? event).bind CompletionEffects.lifetime?) (fun _=>True.intro) body

private theorem lifetime_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Driver.StateHistorySafe Safe (lifetime.arm pid timer delay caller) := by
  intro w a h hi
  exact receipt_quiet _ (base_safe _) (fun r=>Event.armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩)
    (fun _=>True.intro) w a h hi
private theorem lifetime_queue (pid : PeerId) : Driver.StateHistorySafe Safe (lifetime.append pid) := by
  intro w a h hi
  exact receipt_quiet _ (base_safe _) (fun r=>Event.queued ⟨CausalScope.current scope? h,pid,r⟩)
    (fun _=>True.intro) w a h hi

macro "cookie_lifetime_step" : tactic => `(tactic| first
  | (driver_history_head LifetimeEffects.Ops.arm; exact lifetime_arm _ _ _ _)
  | (driver_history_head LifetimeEffects.Ops.append; exact lifetime_queue _)
  | (first | driver_history_head LifetimeEffects.Ops.step | driver_history_head LifetimeEffects.Ops.peer
           | driver_history_head LifetimeEffects.Ops.keypair | driver_history_head LifetimeEffects.Ops.modifyPeer
           | driver_history_head LifetimeEffects.Ops.guard | driver_history_head LifetimeEffects.Ops.get
           | driver_history_head LifetimeEffects.Ops.put
     exact base_safe _)
  | driver_state_history_step)

private theorem lifetime_modify (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Driver.StateHistorySafe Safe (LifetimeEffects.modifyWith lifetime site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' cookie_lifetime_step
private theorem lifetime_traversal (pid : PeerId) :
    Driver.StateHistorySafe Safe (LifetimeEffects.traversalWith lifetime pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head LifetimeEffects.modifyWith; exact lifetime_modify _ _ _ _)
    | cookie_lifetime_step
private theorem lifetime_data (pid : PeerId) : Driver.StateHistorySafe Safe (LifetimeEffects.dataSentWith lifetime pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' cookie_lifetime_step
private theorem lifetime_queued (pid : PeerId) (retry : Bool) :
    Driver.StateHistorySafe Safe (LifetimeEffects.queuedWith lifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' cookie_lifetime_step
private theorem lifetime_fresh (pid : PeerId) : Driver.StateHistorySafe Safe (LifetimeEffects.freshWith lifetime pid) := by
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (driver_history_head LifetimeEffects.queuedWith; exact lifetime_queued _ _)
    | cookie_lifetime_step

private abbrev observed := StagedConservation.SendResult.decorate Event.sendResult
  (CompletionEffects.observed (Event.old ∘ TransmitSecurity.Journal.completionEvent) completion? scope? Event.armed Event.queued)

private theorem old_completion (body : PrefixM Completion.Event α) : Driver.ProductHistorySafe Safe
    (focusPrefix (Event.old ∘ TransmitSecurity.Journal.completionEvent) completion? body) :=
  quiet_product (Event.old ∘ TransmitSecurity.Journal.completionEvent) completion? (fun _=>True.intro) body

private theorem product_receipt (body : PrefixM Event α) (safe : Driver.ProductHistorySafe Safe body)
    (record : RunWitness α→Event) (quiet : ∀r,Unchecked (record r)) :
    Driver.ProductHistorySafe Safe (receiptObserved body record) := by
  unfold receiptObserved
  exact Driver.History.product_bind safe.captureObserved fun receipt=>
    Driver.History.product_bind (product_emit (record receipt) (quiet receipt)) fun _=>Driver.History.product_pure _

private theorem product_capture (body : PrefixM Event α) (preserves : Driver.ProductHistorySafe Safe body) :
    Driver.ProductHistorySafe Safe (captureObserved body) := preserves.captureObserved

macro "cookie_completion_step" : tactic => `(tactic| first
  | (driver_history_head focusPrefix; exact old_completion _)
  | (driver_history_head LifetimeEffects.traversalWith; exact Driver.History.product_state (lifetime_traversal _))
  | (driver_history_head LifetimeEffects.dataSentWith; exact Driver.History.product_state (lifetime_data _))
  | (driver_history_head LifetimeEffects.freshWith; exact Driver.History.product_state (lifetime_fresh _))
  | (driver_history_head StagedConservation.SendResult.observed
     apply product_receipt; try (intro r; trivial))
  | (driver_history_head captureObserved; apply product_capture)
  | driver_product_history_step
  | trivial)

private theorem complete (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,StagedConservation.SendResult.decorate,CompletionEffects.observed,CompletionEffects.focused]
  repeat' cookie_completion_step
private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _=>complete pid item)
private theorem completion_body (pid : PeerId) (first : Option (List SkbId)) :
    Driver.ProductHistorySafe Safe (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,StagedConservation.SendResult.decorate,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | cookie_completion_step

theorem transmit (pid : PeerId) : Driver.ProductHistorySafe Safe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [StagedConservation.SendResult.decorate,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.bodySourceWith; exact completion_body _ _)
    | cookie_completion_step

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
