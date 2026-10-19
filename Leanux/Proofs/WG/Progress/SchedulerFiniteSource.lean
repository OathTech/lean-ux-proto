import Leanux.Proofs.WG.Progress.ActivationFiniteSource
import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.SchedulerFinite
open Leanux Leanux.WG Leanux.Env

/-- The copied run is evaluated at the actual entry; its successor is discarded.
Only hidden-input mismatches are classified as an inconsistent candidate. -/
def consistentWith (run : Activation → Leanux.M Unit) (a : Activation) : Leanux.M Bool :=
  fun initial => probeResult initial ((run a).run initial)

theorem consistentWith_original (a : Activation) :
    Activation.consistent a = consistentWith Activation.run a := by
  funext initial
  exact consistent_exact a initial

/-- The existing scheduler-turn factory and the original captured loop bound.
The unchanged NAPI path and all non-callback leaves are structurally finite. -/
def scheduleWith (run : Activation → Leanux.M Unit) (dispatch : Worker → Leanux.M Bool)
    (stack : Option Worker) : Leanux.M Unit := do
  let budget ← recordBudget
  let result ← forIn [0:budget] ((none, ()) : Option Unit × Unit)
    (fun _ _ => scheduleTurnWith run dispatch (consistentWith run) napiSoftirq stack)
  match result.1 with
  | some ret => pure ret
  | none => budgetExhausted "the scheduler loop"

theorem scheduleWith_original (stack : Option Worker) :
    Env.schedule stack = scheduleWith Activation.run Env.dispatch stack := by
  have turn : scheduleTurn stack =
      scheduleTurnWith Activation.run Env.dispatch (consistentWith Activation.run) napiSoftirq stack := by
    have same : Activation.consistent = consistentWith Activation.run :=
      funext consistentWith_original
    rw [← same]
    rfl
  rw [Progress.schedule_source]
  unfold scheduleWith
  simp only [turn]
  rfl
end Leanux.Proofs.WG.Progress.SchedulerFinite

namespace Leanux.Proofs.WG.Progress.SchedulerFinite
open Leanux Leanux.WG

/-- A concrete copied activation trial using the finite worker evaluator. -/
def consistent (a : Activation) : Leanux.M Bool :=
  consistentWith ActivationFinite.run a

theorem consistent_source (a : Activation) :
    Env.Activation.consistent a = consistent a := by
  rw [consistentWith_original]
  unfold consistent
  have same : Env.Activation.run = ActivationFinite.run := funext ActivationFinite.run_source
  rw [same]

/-- The original scheduler, using finite activation evaluation in both
committed calls and discarded consistency trials. The captured budget,
ambiguous-resumption refusal and every other native Stop remain unchanged. -/
def schedule (stack : Option Worker := none) : Leanux.M Unit :=
  scheduleWith ActivationFinite.run ActivationFinite.dispatch stack

theorem schedule_source (stack : Option Worker) :
    Env.schedule stack = schedule stack := by
  rw [scheduleWith_original]
  unfold schedule
  have sameRun : Env.Activation.run = ActivationFinite.run := funext ActivationFinite.run_source
  have sameDispatch : Env.dispatch = ActivationFinite.dispatch := funext ActivationFinite.dispatch_source
  rw [sameRun, sameDispatch]
end Leanux.Proofs.WG.Progress.SchedulerFinite
