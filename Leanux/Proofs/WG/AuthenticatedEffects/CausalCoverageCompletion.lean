import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageLifetime

/-! Completion enters its own concrete selected-batch scope before native
lifetime effects. Noncompletion polling and drop paths do not fabricate one. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev observed := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem old_completion (body : PrefixM Completion.Event α) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  product_focus (Event.old ∘ Journal.completionEvent) completion?
    (fun event => by cases event <;> rfl)
    (fun event impossible => by cases event <;> exact impossible.elim) body

private theorem complete (pid : PeerId) (item : List SkbId) (live : frames ≠ []) :
    ProductAt frames (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (coverage_head focusPrefix; exact old_completion _)
    | (coverage_head LifetimeEffects.traversalWith; exact product_state _ (lifetime_traversal _ live))
    | (coverage_head LifetimeEffects.dataSentWith; exact product_state _ (lifetime_data_sent _ live))
    | (coverage_head LifetimeEffects.freshWith; exact product_state _ (lifetime_fresh _ live))
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    ProductAt frames (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _ _ live => complete pid item live) frames

private theorem body (pid : PeerId) (first : Option (List SkbId)) : ProductAt frames
    (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (coverage_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | (coverage_head focusPrefix; exact old_completion _)
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

theorem transmit (pid : PeerId) : ProductAt frames (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.observedStep CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (coverage_head CompletionEffects.bodySourceWith; exact body _ _)
    | (coverage_head focusPrefix; exact old_completion _)
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
