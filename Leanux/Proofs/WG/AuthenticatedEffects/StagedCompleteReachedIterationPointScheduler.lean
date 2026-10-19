import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointCoverage

/-! Structural discharge of the scheduler's committed iteration child. Its
native point family is the canonical iteration relation, with the original
activation retained. NAPI and the eight iteration children remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev NapiPoints := World → History → World → History → Prop

def schedulerPoints (inside : ChildPoints) (napi : NapiPoints) : Scheduler.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
    | .iteration activation => ∃ site, Point inside (iterationShape activation) w h site u middle
    | .napi => napi w h u middle

variable {native inside : ChildPoints} {nativeNapi insideNapi : NapiPoints} {Good : History → World → Prop}

noncomputable def scheduler_iteration
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (activation : Activation) :
    Scheduler.Points.ChildSourceContract (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good (.iteration activation) where
  remainder := fun w h u middle point =>
    Classical.choose ((Classical.choose_spec point).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before

noncomputable def scheduler_children
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good)
    (napi : Scheduler.Points.ChildSourceContract (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good .napi) :
    Scheduler.Points.ChildContracts (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good where
  iteration := scheduler_iteration carrierGood children
  napi := napi

/-- Scheduler coverage now reduces its committed iteration leaf to the finite
canonical worker source. The external NAPI contract is still stated exactly. -/
theorem schedule_covered
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good)
    (napi : Scheduler.Points.ChildSourceContract (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good .napi)
    (stack : Option Worker) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (Driver.scheduleObserved hooks stack) w h = (result,last)) :
    Scheduler.Points.Execution (Scheduler.Points.scheduleShape stack) w h result last ∧
      Scheduler.Points.Covered (schedulerPoints native nativeNapi) Good
        (Scheduler.Points.scheduleShape stack) w h ∧
      Scheduler.Points.Remainders (scheduler_children carrierGood children napi)
        (Scheduler.Points.scheduleShape stack) w h :=
  Scheduler.Points.schedule_covered carrierGood (scheduler_children carrierGood children napi) stack before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
