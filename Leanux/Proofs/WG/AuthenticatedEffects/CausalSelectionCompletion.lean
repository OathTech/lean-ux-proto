import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionLifetime

/-! Completion preserves positional work/timer selection evidence, including
socket prefixes retained before a later Stop. Its own scope is a distinct kind. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev observed := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem old_completion (body : PrefixM Completion.Event α) : Driver.ProductHistorySafe Safe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  quiet_product (Event.old ∘ Journal.completionEvent) completion? (fun event => by cases event <;> trivial) body

private theorem product_capture (body : PrefixM Event α) (preserves : Driver.ProductHistorySafe Safe body) :
    Driver.ProductHistorySafe Safe (captureObserved body) := preserves.captureObserved

macro "selection_completion_step" : tactic => `(tactic| first
  | (driver_history_head focusPrefix; exact old_completion _)
  | (driver_history_head LifetimeEffects.traversalWith; exact Driver.History.product_state (lifetime_traversal _))
  | (driver_history_head LifetimeEffects.dataSentWith; exact Driver.History.product_state (lifetime_data_sent _))
  | (driver_history_head LifetimeEffects.freshWith; exact Driver.History.product_state (lifetime_fresh _))
  | (driver_history_head captureObserved; apply product_capture)
  | driver_product_history_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' selection_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    Driver.ProductHistorySafe Safe (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) (fun _ => True.intro) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) :
    Driver.ProductHistorySafe Safe (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | selection_completion_step

theorem transmit (pid : PeerId) : Driver.ProductHistorySafe Safe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.observedStep CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.bodySourceWith; exact body _ _)
    | selection_completion_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
