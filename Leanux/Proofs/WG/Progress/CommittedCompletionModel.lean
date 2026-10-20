import Leanux.Proofs.WG.Progress.CommittedRunModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns

/-- This actual activation call returns normally, possibly by yielding. -/
def NormalReceipt (receipt : Receipt) : Prop :=
  ∃ final, receipt.exit.erase = .ok ((),final)

/-- Every committed activation in this journal returns normally. Failed outer
executions need not satisfy this predicate: their last receipt may be a Stop. -/
def NormalHistory (history : List Receipt) : Prop :=
  ∀ receipt ∈ history, NormalReceipt receipt

end Leanux.Proofs.WG.Progress.CommittedRuns
