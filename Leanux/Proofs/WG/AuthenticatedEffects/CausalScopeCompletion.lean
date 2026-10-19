import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeLifetime

/-! The native completion source restores its incoming lexical stack on
normal completion and retains a well-formed stack on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev observed := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem old_completion (body : PrefixM Completion.Event α) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  product_focus (Event.old ∘ Journal.completionEvent) completion? (fun event => by cases event <;> rfl) body

macro "scope_balanced_completion_step" : tactic => `(tactic| first
  | (scope_balance_head focusPrefix; exact old_completion _)
  | (scope_balance_head LifetimeEffects.traversalWith; exact product_state _ (lifetime_traversal _))
  | (scope_balance_head LifetimeEffects.dataSentWith; exact product_state _ (lifetime_data_sent _))
  | (scope_balance_head LifetimeEffects.freshWith; exact product_state _ (lifetime_fresh _))
  | (scope_balance_head captureObserved; apply product_capture)
  | scope_product_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    ProductSafe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' scope_balanced_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    ProductSafe (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) :
    ProductSafe (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (scope_balance_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | scope_balanced_completion_step

theorem transmit (pid : PeerId) : ProductSafe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.observedStep CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (scope_balance_head CompletionEffects.bodySourceWith; exact body _ _)
    | scope_balanced_completion_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
