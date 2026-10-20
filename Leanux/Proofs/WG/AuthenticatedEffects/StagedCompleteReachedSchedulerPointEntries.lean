import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointCoverage

/-! Concrete entry adapters lift literal original range visits and selected
activation paths into the canonical source-point relation. They require only
successful earlier prefixes, not a successful enclosing run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {native inside : ChildPoints}

/-- Original occupancy and refill reads plus a yielded range prefix reach the same
worker-step point, regardless of what the later iteration or finish does. -/
theorem run_visit (a : Activation)
    (read : runPrefix (liftPrefix (Env.Activation.occupancy a)) w h = (.ok (occupancy,u),middle))
    (refillRead : runPrefix (liftPrefix Env.Activation.refills) u middle = (.ok (refills,ready),prepared))
    (visit : LoopVisit (runStepShape occupancy) (Scheduler.indices (occupancy + refills + 1))
      (none,a) ready prepared index acc v last)
    (point : Point inside (runStepShape occupancy index acc) v last site x ending) :
    ∃ enclosingSite, Point inside (runShape a) w h enclosingSite x ending := by
  obtain ⟨loopSite,loopPoint⟩ := visit.point point
  refine ⟨.marked (.run a) (.right (.right (.left loopSite))),?_⟩
  apply Point.marked
  apply Point.source_mpr (run_factor a)
  apply Point.right (.native (.reading (ProductRead.occupancyShape a))) _ read
  apply Point.right (.native (.reading ProductRead.refillsShape)) _ refillRead
  apply Point.source_mpr (runBody_list a occupancy refills)
  exact .left _ loopPoint

/-- The budget is the value returned at the original record site; the visited
choice is from that same finite schedule range and native successful prefix. -/
theorem schedule_visit (stack : Option Worker)
    (read : runPrefix (liftPrefix recordBudget) w h = (.ok (budget,u),middle))
    (visit : LoopVisit (scheduleStepShape stack budget) (Scheduler.indices budget)
      (none,()) u middle index acc v last)
    (point : Point inside (scheduleStepShape stack budget index acc) v last site x ending) :
    ∃ enclosingSite, Point inside (scheduleShape stack) w h enclosingSite x ending := by
  obtain ⟨loopSite,loopPoint⟩ := visit.point point
  refine ⟨.marked (.schedule stack) (.right (.left loopSite)),?_⟩
  apply Point.marked
  apply Point.source_mpr (schedule_factor stack)
  apply Point.right (.native .budget) _ read
  apply Point.source_mpr (scheduleBody_list stack budget)
  exact .left _ loopPoint

/-- Dispatch reaches a run only after the actual choose prefix has completed,
including TX work-list removal and sectionStart at their original sites. -/
theorem dispatched_run (worker : Worker)
    (chosen : runPrefix (dispatchChoose worker) w h = (.ok (some a,u),middle))
    (point : Point inside (runShape a) u middle site v last) :
    Point inside (dispatchShape worker) w h (.marked (.dispatch worker) (.right (.left site))) v last := by
  apply Point.marked
  apply Point.source_mpr (dispatch_factor worker)
  apply Point.right (dispatchChooseShape worker) _ chosen
  exact .left _ point

/-- A source-selected choice reaches its actual dispatch/resume/NAPI body with
the identical native entry world and original continuation. -/
theorem chosen_body (stack : Option Worker) (budget index : Nat) (acc : ScheduleState)
    (chosen : runPrefix (choose stack) w h = (.ok (choice,u),middle))
    (point : Point inside (performShape choice) u middle site v last) :
    Point inside (scheduleStepShape stack budget index acc) w h
      (.marked (.scheduleIndex stack budget index) (.right site)) v last :=
  .marked _ (.right (chooseShape stack) performShape chosen point)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
