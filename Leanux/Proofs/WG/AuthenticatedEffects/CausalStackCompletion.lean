import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackLifetime

/-! Actual transmit completions preserve prior stack-input origins through Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev observed := completionOps

private theorem old_completion (body : PrefixM Completion.Event α) : Driver.ProductHistorySafe Safe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  quiet_product (Event.old ∘ Journal.completionEvent) completion? (fun event => by cases event <;> rfl) body

private theorem product_capture (body : PrefixM Event α) (preserves : Driver.ProductHistorySafe Safe body) :
    Driver.ProductHistorySafe Safe (captureObserved body) := preserves.captureObserved

private theorem result_receipt (body : PrefixM Event α)
    (safe : Driver.ProductHistorySafe Safe body) (record : RunWitness α → Event)
    (quiet : ∀ r, Quiet (record r)) :
    Driver.ProductHistorySafe Safe (receiptObserved body record) := by
  unfold receiptObserved
  apply Driver.History.product_bind safe.captureObserved
  intro r
  have emitted : Driver.ProductHistorySafe Safe (emitPrefix (record r)) := by
    intro w h hi
    have good := hi.emit (record r) (quiet r)
    exact ⟨[record r],rfl,good,good⟩
  exact Driver.History.product_bind emitted (fun _ => Driver.History.product_pure r.value)

private theorem actual_release (peer : Option PeerId) : Driver.ProductHistorySafe Safe
    (HandshakeSecurity.StagedDisposal.TxSource.releaseObserved txEvent txEvent? Event.stagedDisposal peer) :=
  Driver.History.product_state (CallbackHistory.peer _ _
    (fun body => quiet_state
      (HandshakeSecurity.StagedDisposal.TxSource.peerEncode txEvent)
      (HandshakeSecurity.StagedDisposal.TxSource.peerDecode txEvent?)
      (fun _ => rfl) body)
    (fun event => emit_quiet (.stagedDisposal event) rfl) peer)

private theorem actual_dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Driver.ProductHistorySafe Safe (completionOps.dispose pid item key) :=
  CallbackHistory.tx_dispose
    (fun body => quiet_product txEvent txEvent? (fun _ => rfl) body) actual_release pid item key

private theorem actual_dead (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    Driver.ProductHistorySafe Safe
      (HandshakeSecurity.StagedConservation.Terminal.deadObserved txEvent txEvent?
        Event.stagedDisposal Event.terminalDrop pid item head) :=
  CallbackHistory.dead
    (fun body => quiet_product txEvent txEvent? (fun _ => rfl) body) actual_release
    (fun receipt => product_emit (.terminalDrop receipt) rfl) pid item head

macro "stack_origin_completion_step" : tactic => `(tactic| first
  | (driver_history_head HandshakeSecurity.StagedDisposal.TxSource.dispose; exact actual_dispose _ _ _)
  | (driver_history_head HandshakeSecurity.StagedConservation.Terminal.deadObserved; exact actual_dead _ _ _)
  | (driver_history_head receiptObserved; refine result_receipt _ ?_ _ (fun _ => rfl))
  | (driver_history_head focusPrefix; exact old_completion _)
  | (driver_history_head LifetimeEffects.traversalWith; exact Driver.History.product_state (lifetime_traversal _))
  | (driver_history_head LifetimeEffects.dataSentWith; exact Driver.History.product_state (lifetime_data_sent _))
  | (driver_history_head LifetimeEffects.freshWith; exact Driver.History.product_state (lifetime_actual_fresh _))
  | (driver_history_head captureObserved; apply product_capture)
  | driver_product_history_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' stack_origin_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) (fun _ => rfl) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) :
    Driver.ProductHistorySafe Safe (HandshakeSecurity.StagedConservation.Terminal.bodyWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed)
      (HandshakeSecurity.StagedConservation.Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop) pid first) := by
  unfold HandshakeSecurity.StagedConservation.Terminal.bodyWith TxDisposition.andObs
  simp only [observed,completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | stack_origin_completion_step

theorem transmit (pid : PeerId) : Driver.ProductHistorySafe Safe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit HandshakeSecurity.StagedConservation.Terminal.stepWith
  simp only [completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head HandshakeSecurity.StagedConservation.Terminal.bodyWith; exact body _ _)
    | stack_origin_completion_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
