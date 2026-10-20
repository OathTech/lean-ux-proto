import Leanux.Proofs.WG.Progress.CommittedInitializedCompletionSource
import Leanux.Proofs.WG.Progress.CommittedRecordClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged RecordSuffix

/-- Acceptance of the original initialized trace supplies normality of every
committed dispatch/resume call. The caller need not assume each receipt's
success separately. Yielded activations count as normal calls here. -/
theorem original_initialized_normal_receipts (trace : Trace) (placeholders : Bool)
    (json : Json) (accepted : Runner.executeTrace trace placeholders = .ok json) :
    NormalHistory (inspection trace placeholders).2 := by
  have output := inspection_json trace placeholders
  rw [accepted] at output
  change NormalHistory (runPrefixOuter (observed trace placeholders) []).2
  cases actual : runPrefixOuter (observed trace placeholders) [] with
  | mk result history =>
    cases result with
    | error stop =>
      simp only [inspection, actual, Except.map] at output
      cases output
    | ok pair =>
      obtain ⟨value,final⟩ := pair
      exact observed_normal trace placeholders value final history actual

/-- Each actual committed activation of an accepted trace has a normal final
projection. When its own entry has supplied records, that call consumes a
strict suffix; no per-receipt success premise remains. -/
theorem original_initialized_completed_record_decrease
    (trace : Trace) (placeholders : Bool) (json : Json)
    (accepted : Runner.executeTrace trace placeholders = .ok json) :
    ∀ receipt ∈ (inspection trace placeholders).2,
      ∃ final, receipt.exit.erase = .ok ((),final) ∧
        ∀ records, receipt.before.ambient.hidden = some records →
          StrictTail records final.ambient.hidden := by
  intro receipt member
  obtain ⟨final,normal⟩ := original_initialized_normal_receipts trace placeholders json accepted receipt member
  refine ⟨final,normal,?_⟩
  intro records present
  exact (inspection_source trace placeholders receipt member).record_decrease
    records final present normal

end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
