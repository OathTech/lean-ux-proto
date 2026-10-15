import Leanux.Proofs.WG.Campaign2.View
import Leanux.Runner

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner Campaign2

/-- A successfully checked operation boundary, after the original ambient strip. -/
structure RunnerBoundary where
  index : Nat
  result : Int
  after : Snapshot

/-- Exactly the three per-operation guards of the pinned runner. No worker
queue, pending-work or scheduled-NAPI emptiness is included. -/
def RunnerBoundaryClean (cut : RunnerBoundary) : Prop :=
  (cut.after.ambient.hidden = none ∨ cut.after.ambient.hidden = some []) ∧
  cut.after.ambient.suspended = [] ∧ cut.after.wg.netRxRaised = false

structure RunnerBoundaryAudit where
  output : Lean.Json
  boundaries : List RunnerBoundary

end Leanux.Proofs.WG.Progress
