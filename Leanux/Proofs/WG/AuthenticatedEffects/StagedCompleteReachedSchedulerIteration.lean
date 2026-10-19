import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPaths

/-! The committed dispatch or resumed activation joins the actual schedule
prefix to a literal run-loop prefix. The exact remaining loop is retained,
including later Stop, rather than replaced by an arbitrary factor witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

structure DispatchPath (worker : Worker) (w : World) (history : List Event)
    (activation : Activation) (u : World) (middle : List Event) where
  chosen : runPrefix (dispatchChoose worker) w history = (.ok (some activation,u),middle)

theorem DispatchPath.carrier (path : DispatchPath worker w history activation u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u :=
  checked_normal (dispatchChoose_checked worker) before path.chosen

theorem bind_run_equal {left right : PrefixM Event α} (next : α → PrefixM Event β)
    (same : runPrefix left w history = runPrefix right u middle) :
    runPrefix (left >>= next) w history = runPrefix (right >>= next) u middle := by
  rw [runPrefix_bind,runPrefix_bind,same]

def finishSchedule (stack : Option Worker) (remaining : List Nat) : PrefixM Event Unit :=
  forIn remaining (none,()) (scheduleStep stack) >>= scheduleFinish

theorem SchedulePath.dispatch_continuation
    (selected : SchedulePath stack w history (.dispatch worker required) v selectedHistory)
    (dispatched : DispatchPath worker v selectedHistory activation u middle) :
    runPrefix (Driver.scheduleObserved hooks stack) w history =
      runPrefix (SourceScheduler.run iteration activation >>= fun _ =>
        finishSchedule stack selected.remaining) u middle := by
  rw [selected.continuation]
  simp only [perform,bind_assoc]
  rw [dispatch_factor,bind_assoc,runPrefix_bind,dispatched.chosen]
  dsimp only
  cases required <;> simp only [dispatchAfter,bind_assoc,pure_bind,Bool.not_true,
    Bool.false_eq_true,↓reduceIte,scheduleAfter,finishSchedule]

theorem SchedulePath.resumed_continuation
    (selected : SchedulePath stack w history (.resumed activation) u middle) :
    runPrefix (Driver.scheduleObserved hooks stack) w history =
      runPrefix (SourceScheduler.run iteration activation >>= fun _ =>
        finishSchedule stack selected.remaining) u middle := by
  rw [selected.continuation]
  simp only [perform,bind_assoc,pure_bind,scheduleAfter,finishSchedule]

inductive IterationPath (stack : Option Worker) (w : World) (history : List Event)
    (active : Activation) (u : World) (middle : List Event) : Type where
  | dispatched {worker required v selectedHistory activation v' runHistory}
      (selected : SchedulePath stack w history (.dispatch worker required) v selectedHistory)
      (dispatch : DispatchPath worker v selectedHistory activation v' runHistory)
      (running : RunPath activation v' runHistory active u middle)
  | resumed {activation v selectedHistory}
      (selected : SchedulePath stack w history (.resumed activation) v selectedHistory)
      (running : RunPath activation v selectedHistory active u middle)

def iterationEntryPrefix (stack : Option Worker) (scheduleCount runCount : Nat) :
    PrefixM Event (Option RunState) := do
  match ← scheduleEntryPrefix stack scheduleCount with
  | .dispatch worker _ =>
    match ← dispatchChoose worker with
    | none => return none
    | some activation => return some (← runEntryPrefix activation runCount)
  | .resumed activation => return some (← runEntryPrefix activation runCount)
  | _ => return none

def IterationPath.scheduleCount (path : IterationPath stack w history active u middle) : Nat :=
  match path with
  | .dispatched selected _ _ => selected.done.length
  | .resumed selected _ => selected.done.length

def IterationPath.runCount (path : IterationPath stack w history active u middle) : Nat :=
  match path with
  | .dispatched _ _ running => running.done.length
  | .resumed _ running => running.done.length

def IterationPath.tag (path : IterationPath stack w history active u middle) : Option Unit :=
  match path with
  | .dispatched _ _ running => running.tag
  | .resumed _ running => running.tag

def RunPath.initialActivation (_path : RunPath activation w history active u middle) : Activation := activation

def IterationPath.afterIteration (path : IterationPath stack w history active u middle)
    (result : IterResult) : PrefixM Event Unit :=
  match path with
  | .dispatched selected _ running => do
    iterationTail active result >>= runAfter running.initialActivation running.occupancy running.remaining
    finishSchedule stack selected.remaining
  | .resumed selected running => do
    iterationTail active result >>= runAfter running.initialActivation running.occupancy running.remaining
    finishSchedule stack selected.remaining

theorem IterationPath.carrier (path : IterationPath stack w history active u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u := by
  cases path with
  | dispatched selected dispatch running =>
    exact running.carrier (dispatch.carrier (selected.carrier before))
  | resumed selected running => exact running.carrier (selected.carrier before)

theorem IterationPath.prefix (path : IterationPath stack w history active u middle) :
    runPrefix (iterationEntryPrefix stack path.scheduleCount path.runCount) w history =
      (.ok (some (path.tag,active),u),middle) := by
  cases path with
  | dispatched selected dispatch running =>
    simp only [IterationPath.scheduleCount,IterationPath.runCount,IterationPath.tag]
    rw [iterationEntryPrefix,runPrefix_bind,selected.prefix]
    change runPrefix (dispatchChoose _ >>= _) _ _ = _
    rw [runPrefix_bind,dispatch.chosen]
    change runPrefix (runEntryPrefix _ _ >>= fun acc => pure (some acc)) _ _ = _
    rw [runPrefix_bind,running.prefix]
    rfl
  | resumed selected running =>
    simp only [IterationPath.scheduleCount,IterationPath.runCount,IterationPath.tag]
    rw [iterationEntryPrefix,runPrefix_bind,selected.prefix]
    change runPrefix (runEntryPrefix _ _ >>= fun acc => pure (some acc)) _ _ = _
    rw [runPrefix_bind,running.prefix]
    rfl

/-- The source-selected activation entry has the concrete carrier and a
fixed successful prefix. Its original scheduler continuation is preserved
for both returned and stopped executions. -/
theorem IterationPath.continuation (path : IterationPath stack w history active u middle) :
    runPrefix (Driver.scheduleObserved hooks stack) w history =
      runPrefix (Driver.iterationObserved hooks active >>= path.afterIteration) u middle := by
  change _ = runPrefix (Driver.iterationObserved hooks active >>= fun result => path.afterIteration result) u middle
  cases path with
  | dispatched selected dispatch running =>
    rw [selected.dispatch_continuation dispatch,
      bind_run_equal (fun _ => finishSchedule stack selected.remaining) running.continuation]
    simp only [bind_assoc,IterationPath.afterIteration,RunPath.initialActivation,iteration]
  | resumed selected running =>
    rw [selected.resumed_continuation,
      bind_run_equal (fun _ => finishSchedule stack selected.remaining) running.continuation]
    simp only [bind_assoc,IterationPath.afterIteration,RunPath.initialActivation,iteration]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
