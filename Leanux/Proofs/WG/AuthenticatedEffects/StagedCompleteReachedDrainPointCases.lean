import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointSource

/-! Both directions of the source decomposition. The records below are derived
from, and replay to, the actual front, step, loop and original drain runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

theorem FrontExecution.run (path : FrontExecution w history result last) :
    runPrefix front w history = (result,last) := by
  cases path <;> simp only [front_factor,runPrefix_bind,afterRead, *]
  all_goals simp only [Bool.false_eq_true,↓reduceIte,runPrefix_bind,runPrefix_pure, *]

theorem front_cases (performed : runPrefix front w history = (result,last)) :
    FrontExecution w history result last := by
  rw [front_factor,runPrefix_bind] at performed
  cases read : runPrefix frontRead w history with
  | mk out middle =>
    rw [read] at performed
    cases out with
    | error reason => cases performed; exact .readStopped read
    | ok pair =>
      obtain ⟨saved,u⟩ := pair
      by_cases absent : saved.dev.isNone = true
      · simp only [afterRead,absent,↓reduceIte,runPrefix_pure] at performed
        cases performed
        exact .absent read absent
      · have present := Bool.eq_false_iff.mpr absent
        simp only [afterRead,absent,Bool.false_eq_true,↓reduceIte,runPrefix_bind] at performed
        cases checked : runPrefix frontCheck u middle with
        | mk out afterCheck =>
          rw [checked] at performed
          cases out with
          | error reason => cases performed; exact .checkStopped read present checked
          | ok pair =>
            obtain ⟨value,v⟩ := pair
            cases value
            dsimp only at performed
            cases reset : runPrefix frontReset v afterCheck with
            | mk out afterReset =>
              rw [reset] at performed
              cases out with
              | error reason => cases performed; exact .resetStopped read present checked reset
              | ok pair =>
                obtain ⟨value,next⟩ := pair
                cases value
                dsimp only at performed
                cases budget : runPrefix frontBudget next afterReset with
                | mk out afterBudget =>
                  rw [budget] at performed
                  cases out with
                  | error reason => cases performed; exact .budgetStopped read present checked reset budget
                  | ok pair =>
                    obtain ⟨count,final⟩ := pair
                    simp only [runPrefix_pure] at performed
                    cases performed
                    exact .ready read present checked reset budget

theorem StepExecution.run (path : StepExecution index acc w history result last) :
    runPrefix (step index acc) w history = (result,last) := by
  cases path <;> simp only [step,runPrefix_bind, *]
  all_goals simp only [Bool.false_eq_true,↓reduceIte,runPrefix_bind,runPrefix_pure, *]

theorem step_cases (performed : runPrefix (step index acc) w history = (result,last)) :
    StepExecution index acc w history result last := by
  rw [step,runPrefix_bind] at performed
  cases read : runPrefix (liftPrefix (liftWG getDev)) w history with
  | mk out middle =>
    rw [read] at performed
    cases out with
    | error reason => cases performed; exact .readStopped read
    | ok pair =>
      obtain ⟨device,u⟩ := pair
      by_cases empty : device.sendWorkQueue.isEmpty = true
      · simp only [empty,↓reduceIte,runPrefix_bind] at performed
        cases delivered : runPrefix hooks.deliver u middle with
        | mk out after =>
          rw [delivered] at performed
          cases out with
          | error reason => cases performed; exact .deliveryStopped read empty delivered
          | ok pair =>
            obtain ⟨value,v⟩ := pair
            cases value
            dsimp only at performed
            simp only [runPrefix_pure] at performed
            cases performed
            exact .done read empty delivered
      · have nonempty := Bool.eq_false_iff.mpr empty
        simp only [empty,Bool.false_eq_true,↓reduceIte,runPrefix_bind] at performed
        cases sent : runPrefix (Driver.sendWorkerObserved hooks) u middle with
        | mk out after =>
          rw [sent] at performed
          cases out with
          | error reason => cases performed; exact .workerStopped read nonempty sent
          | ok pair =>
            obtain ⟨value,v⟩ := pair
            cases value
            dsimp only at performed
            cases scheduled : runPrefix (Driver.scheduleObserved hooks none) v after with
            | mk out ending =>
              rw [scheduled] at performed
              cases out with
              | error reason => cases performed; exact .scheduleStopped read nonempty sent scheduled
              | ok pair =>
                obtain ⟨value,next⟩ := pair
                cases value
                dsimp only at performed
                simp only [runPrefix_pure] at performed
                cases performed
                exact .yielded read nonempty sent scheduled

theorem LoopExecution.run (path : LoopExecution indices acc w history result last) :
    runPrefix (forIn indices acc step) w history = (result,last) := by
  induction path with
  | nil => rfl
  | stopped current => rw [List.forIn_cons,runPrefix_bind,current.run]
  | done current => rw [List.forIn_cons,runPrefix_bind,current.run]; rfl
  | yielded current remaining ih => rw [List.forIn_cons,runPrefix_bind,current.run]; exact ih

/-- Every actual finite loop, successful or stopped, supplies the entire
ordered source decomposition, including its empty/done/yield alternatives. -/
theorem loop_cases (performed : runPrefix (forIn indices acc step) w history = (result,last)) :
    LoopExecution indices acc w history result last := by
  induction indices generalizing acc w history with
  | nil => simp only [List.forIn_nil,runPrefix_pure] at performed; cases performed; exact .nil
  | cons index indices ih =>
    rw [List.forIn_cons,runPrefix_bind] at performed
    cases current : runPrefix (step index acc) w history with
    | mk out middle =>
      rw [current] at performed
      cases out with
      | error reason => cases performed; exact .stopped (step_cases current)
      | ok pair =>
        obtain ⟨decision,u⟩ := pair
        cases decision with
        | done final =>
          simp only [runPrefix_pure] at performed
          cases performed
          exact .done (step_cases current)
        | yield next => exact .yielded (step_cases current) (ih performed)

theorem Execution.run (path : Execution w history result last) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = (result,last) := by
  cases path with
  | frontStopped entered => rw [source_factor,runPrefix_bind,entered.run]
  | absent entered => rw [source_factor,runPrefix_bind,entered.run]; rfl
  | loopStopped entered loop =>
      rw [source_factor,runPrefix_bind,entered.run]
      change runPrefix (body _) _ _ = _
      rw [body_list,runPrefix_bind,loop.run]
  | finish entered loop performed =>
      rw [source_factor,runPrefix_bind,entered.run]
      change runPrefix (body _) _ _ = _
      rw [body_list,runPrefix_bind,loop.run]
      exact performed

/-- Source coverage for the original send drain includes all completed
iterations and the final stopped or returned operation. Child interiors remain
their explicitly supplied source contracts; this theorem adds no guessed cut. -/
theorem execution_cases
    (performed : runPrefix (Driver.sendWorkersObserved hooks) w history = (result,last)) :
    Execution w history result last := by
  rw [source_factor,runPrefix_bind] at performed
  cases entered : runPrefix front w history with
  | mk out middle =>
    rw [entered] at performed
    cases out with
    | error reason => cases performed; exact .frontStopped (front_cases entered)
    | ok pair =>
      obtain ⟨budget,u⟩ := pair
      cases budget with
      | none => simp only [afterFront,runPrefix_pure] at performed; cases performed; exact .absent (front_cases entered)
      | some budget =>
        change runPrefix (body budget) u middle = _ at performed
        rw [body_list,runPrefix_bind] at performed
        cases loop : runPrefix (forIn (Scheduler.indices budget) (none,()) step) u middle with
        | mk out current =>
          rw [loop] at performed
          cases out with
          | error reason => cases performed; exact .loopStopped (front_cases entered) (loop_cases loop)
          | ok pair =>
            obtain ⟨acc,v⟩ := pair
            exact .finish (front_cases entered) (loop_cases loop) performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
