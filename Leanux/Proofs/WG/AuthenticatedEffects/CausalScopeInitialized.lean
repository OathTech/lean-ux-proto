import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeOrigin
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized

/-! Malformed context is excluded at every prefix of the actual initialized
final journal. Absence and authorization are separate obligations; no root is
manufactured by converting a valid empty stack into a cause. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem prefix_wellFormed (before after : List Event)
    (valid : CausalScope.WellFormed scope? (before ++ after)) :
    CausalScope.WellFormed scope? before := by
  obtain ⟨frames,normal⟩ := valid
  cases value : CausalScope.stack (before.filterMap scope?) with
  | ok old => exact ⟨old,value⟩
  | error error =>
    simp only [List.filterMap_append,CausalScope.stack,List.foldl_append] at normal
    change (after.filterMap scope?).foldl CausalScope.advance
      (CausalScope.stack (before.filterMap scope?)) = .ok frames at normal
    rw [value,CausalScope.fold_error] at normal
    cases normal

theorem initialized_prefix (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ after) :
    CausalScope.WellFormed scope? before := by
  apply prefix_wellFormed before after
  rw [← position]
  exact initialized trace placeholders

theorem current_success (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ after) :
    ∃ token, CausalScope.current scope? before = .ok token := by
  obtain ⟨frames,valid⟩ := initialized_prefix trace placeholders before after position
  exact ⟨frames.head?,by simp only [CausalScope.current,valid,Except.map]⟩

theorem arm_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Arm Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .armed receipt :: after) :
    ∃ token, receipt.cause = .ok token := by
  obtain ⟨token,context⟩ := current_success trace placeholders before (.armed receipt :: after) position
  exact ⟨token,(Receipts.initialized_arm trace placeholders before after receipt position).2.trans context⟩

theorem queue_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Queued Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .queued receipt :: after) :
    ∃ token, receipt.cause = .ok token := by
  obtain ⟨token,context⟩ := current_success trace placeholders before (.queued receipt :: after) position
  exact ⟨token,(Receipts.initialized_queue trace placeholders before after receipt position).2.trans context⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
