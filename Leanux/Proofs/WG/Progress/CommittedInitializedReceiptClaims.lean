import Leanux.Proofs.WG.Progress.CommittedInitializedClaims
import Leanux.Proofs.WG.Progress.CommittedReceiptSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Leanux Leanux.Runner Leanux.Proofs.Logged

/-- Every projected receipt comes from the actual run callback's native entry.
The caller labels are the unchanged dispatch/resume callback arguments; this
theorem does not infer caller context from an arbitrary SourceReceipt. -/
theorem inspection_source (trace : Trace) (placeholders : Bool) :
    SourceHistory (inspection trace placeholders).2 :=
  History.observed_valid SourceHistory run_source_preserves
    (by intro receipt member; cases member) trace placeholders

theorem original_initialized_source_receipts (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (inspection trace placeholders).2,
      SourceReceipt receipt ∧ ActivationExitFacts receipt.activation receipt.exit := by
  refine ⟨inspection_json trace placeholders,?_⟩
  intro receipt member
  have source:=inspection_source trace placeholders receipt member
  exact ⟨source,source.facts⟩

end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
