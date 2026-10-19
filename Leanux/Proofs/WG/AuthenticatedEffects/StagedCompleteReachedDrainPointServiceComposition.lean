import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointResidual
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointDelivery
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointSchedulerComposition

/-! The drain's delivery leaf and scheduler call share their concrete source
relations. Only the actual send worker retains its own child contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def drainPoints (scheduler : Scheduler.Points.ChildPoints) (other : Points.ChildPoints) :
    Points.ChildPoints := fun token w h u middle => match token with
  | .delivery => Service.Points.RootPoints Service.Points.Boundary .delivery w h u middle
  | .scheduler => ∃site,Scheduler.Points.Point scheduler
      (Scheduler.Points.scheduleShape none) w h site u middle
  | .worker => other .worker w h u middle

variable {native inside : Scheduler.Points.ChildPoints}
  {nativeOther insideOther : Points.ChildPoints} {Good : History → World → Prop}

noncomputable def delivery
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w) :
    Points.ChildSourceContract (drainPoints native nativeOther)
      (drainPoints inside insideOther) Good .delivery where
  remainder := Service.Points.deliveryRemainder
  continuation := fun _ _ _ _ point => Service.Points.deliveryRemainder_run point
  coverage := fun _ _ _ _ point => point
  safe := fun _ _ _ _ before point => carrierGood _ _ (Service.Points.delivery_carrier before point)

noncomputable def scheduler
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Scheduler.Points.ChildContracts native inside Good) :
    Points.ChildSourceContract (drainPoints native nativeOther)
      (drainPoints inside insideOther) Good .scheduler where
  remainder := Service.SchedulerComposition.remainder none children
  continuation := fun _ _ _ _ point => Service.SchedulerComposition.remainder_run none children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before

noncomputable def drainChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (scheduling : Scheduler.Points.ChildContracts native inside Good)
    (worker : Points.ChildSourceContract (drainPoints native nativeOther)
      (drainPoints inside insideOther) Good .worker) :
    Points.ChildContracts (drainPoints native nativeOther) (drainPoints inside insideOther) Good :=
  ⟨delivery carrierGood,worker,scheduler carrierGood scheduling⟩

def servicePoints (drain : Points.ChildPoints) (other : Service.Points.ChildPoints) :
    Service.Points.ChildPoints := fun α action token w h u middle => match token with
  | .family .sends => Points.RootPoints drain w h u middle
  | token => other α action token w h u middle

/-- The service drain uses each actual native prefix and the literal
remaining drain, preserving the same history and account at its caller. -/
noncomputable def serviceSends
    {nativeDrain insideDrain : Points.ChildPoints}
    {nativeService insideService : Service.Points.ChildPoints}
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts nativeDrain insideDrain Good) :
    Service.Points.ChildSourceContract (servicePoints nativeDrain nativeService)
      (servicePoints insideDrain insideService) Good (.family .sends) where
  remainder := Points.remainder children
  continuation := fun _ _ _ _ point => Points.remainder_run children point
  coverage := fun _ _ _ _ point => Points.root_coverage children point
  safe := fun _ _ _ _ before point => Points.root_safe carrierGood children before point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Composition
