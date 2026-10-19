import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageLifetime

/-! Completion enters its own concrete selected-batch scope before native
lifetime effects. Noncompletion polling and drop paths do not fabricate one. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private abbrev observed := HandshakeSecurity.StagedConservation.SendResult.decorate Event.sendResult
  (CompletionEffects.observed
    (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued)

private theorem old_completion (body : PrefixM Completion.Event α) (live : frames ≠ []) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  product_focus (Event.old ∘ Journal.completionEvent) completion?
    (fun event => by cases event <;> rfl)
    (fun _ _ => live) body

private theorem result_receipt (body : PrefixM Event α) (safe : ProductAt frames body)
    (record : RunWitness α → Event) (quiet : ∀ r, scope? (record r) = none)
    (unprotected : ∀ r, Protected (record r) → frames ≠ []) :
    ProductAt frames (receiptObserved body record) := by
  unfold receiptObserved
  exact product_bind (product_capture _ safe) (fun r =>
    product_bind (by
      intro w h ready
      have good := ready.emit (quiet r) (unprotected r)
      exact ⟨[record r],rfl,good.1,good⟩) (fun _ => product_pure r.value))

private theorem complete (pid : PeerId) (item : List SkbId) (live : frames ≠ []) :
    ProductAt frames (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (coverage_head receiptObserved; refine result_receipt _ ?_ _ (fun _ => rfl) (fun _ h => h.elim))
    | (coverage_head focusPrefix; exact old_completion _ live)
    | (coverage_head LifetimeEffects.traversalWith; exact product_state _ (lifetime_traversal _ live))
    | (coverage_head LifetimeEffects.dataSentWith; exact product_state _ (lifetime_data_sent _ live))
    | (coverage_head LifetimeEffects.freshWith; exact product_state _ (lifetime_fresh _ live))
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) :
    ProductAt frames (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) True.intro _ (fun _ _ live => complete pid item live) frames

private theorem old_quiet_completion (body : PrefixM Completion.Event α)
    (appends : Appends body) (quiet : HistoryFrame Completion.socket? body) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) := by
  intro w h ready
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap completion?)
  have frame := quiet w (h.filterMap completion?)
  rw [grown] at frame
  have empty : suffix.filterMap Completion.socket? = [] := by
    have sizes := congrArg List.length frame
    simp only [List.filterMap_append,List.length_append] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  have good := ready.quiet (suffix.map (Event.old ∘ Journal.completionEvent)) (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    cases original <;> rfl) (by
    intro event member
    obtain ⟨original,found,rfl⟩ := List.mem_map.mp member
    cases original with
    | disposition value => intro impossible; exact impossible.elim
    | socket receipt =>
      have included : receipt ∈ suffix.filterMap Completion.socket? := List.mem_filterMap.mpr ⟨_,found,rfl⟩
      rw [empty] at included
      cases included)
  have run := focusPrefix_suffix (Event.old ∘ Journal.completionEvent) completion? body w h _ suffix (Prod.ext rfl grown)
  rw [run]
  refine ⟨suffix.map (Event.old ∘ Journal.completionEvent),rfl,good.1,?_⟩
  cases (runPrefix body w (h.filterMap completion?)).1 <;> trivial

private theorem old_step (body : WG.M α) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (liftPrefix (liftWG body))) :=
  old_quiet_completion _ (Appends.lift _) (HistoryFrame.lift _ _)

private theorem old_access (body : MixedM α) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access body)) :=
  old_quiet_completion _ (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)

private theorem old_disposition (body : PrefixM TxDisposition.Event α) : ProductAt frames
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? body)) :=
  old_quiet_completion _ (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)

open Lean Meta Elab Tactic in
elab "coverage_completion_body " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductAt do throwError "not a product coverage contract"
  let arguments := target.getAppArgs
  unless arguments.size > 0 do throwError "missing action"
  let action := arguments.back!.consumeMData.headBeta
  unless action.isAppOf ``focusPrefix do throwError "not a focused completion callback"
  let parts := action.getAppArgs
  unless parts.size > 0 do throwError "missing focused body"
  let body := parts.back!.consumeMData.headBeta
  let .const name _ := body.getAppFn | throwError "not a named body"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless name.toString == expected || name.toString.endsWith ("." ++ expected) do throwError "different body"

private theorem body (pid : PeerId) (first : Option (List SkbId)) : ProductAt frames
    (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (coverage_head receiptObserved; refine result_receipt _ ?_ _ (fun _ => rfl) (fun _ h => h.elim))
    | (coverage_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | (coverage_completion_body liftPrefix; exact old_step _)
    | (coverage_completion_body Completion.access; exact old_access _)
    | (coverage_completion_body focusPrefix; exact old_disposition _)
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

theorem transmit (pid : PeerId) : ProductAt frames (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (coverage_head receiptObserved; refine result_receipt _ ?_ _ (fun _ => rfl) (fun _ h => h.elim))
    | (coverage_head CompletionEffects.bodySourceWith; exact body _ _)
    | (coverage_completion_body liftPrefix; exact old_step _)
    | (coverage_completion_body Completion.access; exact old_access _)
    | (coverage_completion_body focusPrefix; exact old_disposition _)
    | (coverage_head captureObserved; apply product_capture)
    | coverage_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
