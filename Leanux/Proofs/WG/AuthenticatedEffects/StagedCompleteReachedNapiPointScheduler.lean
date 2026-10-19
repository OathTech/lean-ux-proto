import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointCoverage

/-! The scheduler's NAPI leaf and the iteration's two NAPI leaves reduce to
fixed original source witnesses. Other scheduler/iteration children stay explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev IterationPoints := Activation → World → History → World → History → Prop

def schedulerPoints (inside : ChildPoints) (iteration : IterationPoints) : Scheduler.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
    | .iteration activation => iteration activation w h u middle
    | .napi => ∃ site, Point inside softirqShape w h site u middle

variable {native inside : ChildPoints} {nativeIteration insideIteration : IterationPoints}
variable {Good : History → World → Prop}

noncomputable def scheduler_napi
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good) :
    Scheduler.Points.ChildSourceContract (schedulerPoints native nativeIteration)
      (schedulerPoints inside insideIteration) Good .napi where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
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
    exact point.safe carrierGood children before.1

noncomputable def scheduler_children
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (iteration : ∀ activation, Scheduler.Points.ChildSourceContract (schedulerPoints native nativeIteration)
      (schedulerPoints inside insideIteration) Good (.iteration activation)) :
    Scheduler.Points.ChildContracts (schedulerPoints native nativeIteration)
      (schedulerPoints inside insideIteration) Good where
  iteration := iteration
  napi := scheduler_napi carrierGood children

theorem schedule_covered
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (iteration : ∀ activation, Scheduler.Points.ChildSourceContract (schedulerPoints native nativeIteration)
      (schedulerPoints inside insideIteration) Good (.iteration activation))
    (stack : Option Worker) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (Driver.scheduleObserved hooks stack) w h = (result,last)) :
    Scheduler.Points.Execution (Scheduler.Points.scheduleShape stack) w h result last ∧
      Scheduler.Points.Covered (schedulerPoints native nativeIteration) Good
        (Scheduler.Points.scheduleShape stack) w h ∧
      Scheduler.Points.Remainders (scheduler_children carrierGood children iteration)
        (Scheduler.Points.scheduleShape stack) w h :=
  Scheduler.Points.schedule_covered (fun h w before => carrierGood h w before.1)
    (scheduler_children carrierGood children iteration) stack before performed

def iterationPoints (inside : ChildPoints) (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle => match token with
    | .softirq => ∃ site, Point inside softirqShape w h site u middle
    | .irqExit => ∃ site, Point inside irqShape w h site u middle
    | token => other token w h u middle

variable {nativeOther insideOther : Iteration.Points.ChildPoints}

noncomputable def iteration_softirq
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good) :
    Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
      (iterationPoints inside insideOther) Good .softirq where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
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
    exact point.safe carrierGood children before.1

noncomputable def iteration_irq
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good) :
    Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
      (iterationPoints inside insideOther) Good .irqExit where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
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
    exact point.safe carrierGood children before.1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
