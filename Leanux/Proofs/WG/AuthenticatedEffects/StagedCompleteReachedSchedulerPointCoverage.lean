import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointLoops
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointResidual

/-! Public conditional coverage for the original scheduler cluster. Fixed
canonical witnesses expose normal and stopped source decompositions; committed
child interiors remain exactly the two stated native-source obligations. This
is not an initialized whole-mirror conservation theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {native inside : ChildPoints} {Good : History → World → Prop}

abbrev Boundary : ChildPoints := fun _ _ _ _ _ _ _ => False

/-- Native boundaries and child entries/returns preserve the concrete carrier
without an interior coverage premise. This includes silent TX work-list and
suspension changes because their source atoms have explicit checked frames. -/
theorem boundary_carrier (point : Point Boundary shape w h site u middle)
    (before : CompleteProduct.Carrier h w) : CompleteProduct.Carrier middle u := by
  induction point with
  | entry shape => exact before
  | returned shape performed => exact shape.normal before performed
  | interior token point => exact False.elim point
  | reading point => exact point.carrier before
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)
  | marked label point ih => exact ih before

def Remainders (children : ChildContracts native inside Good) {α : Type} {action : PrefixM Event α}
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point native shape w h site u middle →
    ∃ remaining : PrefixM Event α, Residual children shape w h site u middle remaining

/-- Coverage and remainder retain the same fixed source witness and actual
point world/history. A remainder equation alone is never point evidence. -/
theorem source_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (shape : Shape action)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h = (result,last)) :
    Execution shape w h result last ∧ Covered native Good shape w h ∧ Remainders children shape w h :=
  ⟨execution_cases shape performed,covered carrierGood children shape before,
    fun _ _ _ point => point.residual children⟩

theorem run_cases (a : Activation)
    (performed : runPrefix (SourceScheduler.run iteration a) w h = (result,last)) :
    Execution (runShape a) w h result last := execution_cases _ performed

theorem dispatch_cases (worker : Worker)
    (performed : runPrefix (SourceScheduler.dispatch iteration worker) w h = (result,last)) :
    Execution (dispatchShape worker) w h result last := execution_cases _ performed

theorem schedule_cases (stack : Option Worker)
    (performed : runPrefix (Driver.scheduleObserved hooks stack) w h = (result,last)) :
    Execution (scheduleShape stack) w h result last := execution_cases _ performed

/-- Original worker runs retain all actual entered iterations, including an
ended/yielded activation or an error before the bound is exhausted. -/
theorem run_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (a : Activation)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (SourceScheduler.run iteration a) w h = (result,last)) :
    Execution (runShape a) w h result last ∧ Covered native Good (runShape a) w h ∧
      Remainders children (runShape a) w h := source_covered carrierGood children _ before performed

/-- Original dispatch preserves its actual read, TX owner resolution/work-list
removal, section-start marker and ensuing committed activation in source order. -/
theorem dispatch_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (worker : Worker)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (SourceScheduler.dispatch iteration worker) w h = (result,last)) :
    Execution (dispatchShape worker) w h result last ∧ Covered native Good (dispatchShape worker) w h ∧
      Remainders children (dispatchShape worker) w h := source_covered carrierGood children _ before performed

/-- Every fixed canonical scheduler point is covered on successful and stopped
runs, conditional on committed iteration and NAPI interior coverage. Record
budget, choices, original ranges and consistency trials stay in the source. -/
theorem schedule_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (stack : Option Worker)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (Driver.scheduleObserved hooks stack) w h = (result,last)) :
    Execution (scheduleShape stack) w h result last ∧ Covered native Good (scheduleShape stack) w h ∧
      Remainders children (scheduleShape stack) w h := source_covered carrierGood children _ before performed

/-- The run-loop index is the original range position. Its committed child is
the actual activation stored in the source accumulator. -/
theorem run_step_entry (occupancy index : Nat) (acc : RunState) :
    Point inside (runStepShape occupancy index acc) w h
      (.marked (.runIndex acc.2 occupancy index) (.left .entry)) w h :=
  .marked _ (.left _ (.entry _))

theorem run_step_return (occupancy index : Nat) (acc : RunState)
    (performed : runPrefix (iteration acc.2) w h = (.ok (result,u),middle)) :
    Point inside (runStepShape occupancy index acc) w h
      (.marked (.runIndex acc.2 occupancy index) (.left .returned)) u middle :=
  .marked _ (.left _ (.returned _ performed))

theorem run_step_interior (occupancy index : Nat) (acc : RunState)
    (nativePoint : native _ _ (.iteration acc.2) w h u middle) :
    Point native (runStepShape occupancy index acc) w h
      (.marked (.runIndex acc.2 occupancy index) (.left .interior)) u middle :=
  .marked _ (.left _ (.interior _ nativePoint))

theorem napi_entry : Point inside (performShape .napi) w h (.left .entry) w h :=
  .left _ (.entry _)

theorem napi_return
    (performed : runPrefix (Driver.softirqObserved hooks) w h = (.ok (result,u),middle)) :
    Point inside (performShape .napi) w h (.left .returned) u middle :=
  .left _ (.returned _ performed)

theorem napi_interior (nativePoint : native _ _ .napi w h u middle) :
    Point native (performShape .napi) w h (.left .interior) u middle :=
  .left _ (.interior _ nativePoint)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
