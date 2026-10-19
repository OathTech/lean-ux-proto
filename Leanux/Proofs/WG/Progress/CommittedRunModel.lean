import Leanux.Proofs.WG.Progress.ActivationExitModel

/-! Projected receipts of actual committed activation calls. Consistency trials
are excluded by the scheduler's existing callback boundary. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux

inductive Origin where
  | dispatch
  | resume
  deriving DecidableEq

structure Receipt where
  origin : Origin
  activation : Activation
  before : Campaign2.Product.Snapshot
  exit : ActivationExitAudit Campaign2.Product.Snapshot

def Valid (r : Receipt) : Prop := ActivationExitFacts r.activation r.exit

def ValidHistory (history : List Receipt) : Prop := ∀ r ∈ history, Valid r

end Leanux.Proofs.WG.Progress.CommittedRuns
