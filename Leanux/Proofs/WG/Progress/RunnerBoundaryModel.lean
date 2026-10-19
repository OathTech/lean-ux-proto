import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.Runner

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner Campaign2

/-- A successfully checked operation boundary, after the original ambient strip. -/
structure RunnerBoundary where
  index : Nat
  result : Int
  after : Campaign2.Product.Snapshot

/-- The original four per-operation checks. Pending work must be empty when
this actual cut has supplied records; placeholder pending work and scheduled
NAPI are not constrained by the runner guards alone. -/
def RunnerBoundaryClean (cut : RunnerBoundary) : Prop :=
  (cut.after.ambient.hidden = none ∨ cut.after.ambient.hidden = some []) ∧
  cut.after.ambient.suspended = [] ∧ cut.after.wg.netRxRaised = false ∧
  (cut.after.ambient.hidden.isSome = true → cut.after.ambient.pendingWork = [])

structure RunnerBoundaryAudit where
  output : Lean.Json
  boundaries : List RunnerBoundary

end Leanux.Proofs.WG.Progress
