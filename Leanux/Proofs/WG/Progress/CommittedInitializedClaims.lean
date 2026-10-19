import Leanux.Proofs.WG.Progress.CommittedInitializedModel
import Leanux.Proofs.WG.Progress.CommittedInitializedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged

/-- Public state projection of the same initialized execution. No final state is
invented for a Stop; its indexed error and actual receipt prefix remain. -/
def inspection (trace : Trace) (placeholders : Bool := false) : Inspection :=
  let result:=runPrefixOuter (observed trace placeholders) []
  (result.1.map (fun (json,world)=>(json,Campaign2.Product.snapshot world)),result.2)

theorem inspection_json (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders := by
  dsimp only [inspection]
  rw [observed_erases trace placeholders []]
  have original := Configuration.sourceRunner_json trace placeholders
  cases result : Configuration.sourceRunner trace placeholders <;>
    simpa only [result,Except.map] using original

theorem original_initialized_journal (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (inspection trace placeholders).2,
      ActivationExitFacts receipt.activation receipt.exit :=
  ⟨inspection_json trace placeholders,observed_valid trace placeholders⟩

end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
