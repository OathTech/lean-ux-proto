import Leanux.Proofs.WG.Progress.SchedulerFiniteSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.SchedulerFinite
open Leanux

/-- Exact finite evaluation of the actual consistency trial. It preserves
discarded successors, hidden-error rejection and propagation of other Stops. -/
theorem original_consistent_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.consistent a) (consistent a) := by
  rw [consistent_source]
  intro w pre
  rfl

/-- Every original scheduler outcome agrees with the finite evaluator.
This retains exhaustion and ambiguity errors and does not prove successful
completion, sufficient activation occupancy, or whole-run service. -/
theorem original_schedule_finite (stack : Option Worker) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.schedule stack) (schedule stack) := by
  rw [schedule_source]
  intro w pre
  rfl
end Leanux.Proofs.WG.Progress.SchedulerFinite
