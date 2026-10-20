import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointResidual
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointLoops

/-! Service roots have canonical original-source coverage and exact residuals.
The seven deeper callbacks remain explicit native-interior contracts. Native
subsystem atoms expose actual entry/normal-return boundaries; this file does
not claim every lower-level primitive interior or initialized T2 closure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

inductive Root where
  | idle | advance | delivery | crypt
  | timers (bound : UInt64)
  | placeholders (bound : UInt64)

def Root.Result : Root → Type
  | .timers _ => Bool
  | _ => Unit

def Root.action (root : Root) : PrefixM Event root.Result := match root with
  | .idle => Driver.idleTimersObserved hooks
  | .advance => Driver.afterAdvanceObserved hooks
  | .delivery => hooks.deliver
  | .crypt => Driver.cryptObserved hooks
  | .timers bound => Driver.timersObserved hooks bound
  | .placeholders bound => Driver.placeholderTimersObserved hooks bound

noncomputable def canonical (root : Root) : Shape root.action := match root with
  | .idle => idleShape
  | .advance => advanceShape
  | .delivery => deliveryShape
  | .crypt => cryptShape
  | .timers bound => timersShape bound
  | .placeholders bound => placeholderShape bound

def Boundary : ChildPoints := fun _ _ _ _ _ _ _=>False

theorem boundary_carrier (before : CompleteProduct.Carrier h w)
    (point : Point Boundary shape w h site u middle) : CompleteProduct.Carrier middle u := by
  induction point with
  | entry => exact before
  | returned shape performed => exact shape.normal before performed
  | delete point => exact point.carrier before
  | reading point => exact point.carrier before
  | interior _ impossible => cases impossible
  | left _ _ ih => exact ih before
  | right head _ leading _ ih => exact ih (head.normal before leading)
  | marked _ _ ih => exact ih before

theorem service_execution (root : Root) {result : Result root.Result}
    (performed : runPrefix root.action w h=(result,last)) :
    Execution (canonical root) w h result last := execution_cases _ performed

theorem service_boundary (root : Root) (before : CompleteProduct.Carrier h w)
    (point : Point Boundary (canonical root) w h site u middle) : CompleteProduct.Carrier middle u :=
  boundary_carrier before point

theorem service_covered (root : Root)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w) :
    Covered native Good (canonical root) w h := covered carrierGood children _ before

theorem service_remainder (root : Root) (children : ChildContracts native inside Good)
    (point : Point native (canonical root) w h site u middle) :
    ∃remaining,Residual children (canonical root) w h site u middle remaining ∧
      runPrefix root.action w h=runPrefix remaining u middle := by
  obtain ⟨remaining,residual⟩ := point.residual children
  exact ⟨remaining,residual,residual.run⟩

/-- Exact native points are indexed by the selected canonical source root,
not by an arbitrary prefix/suffix factorization. -/
def RootPoints (points : ChildPoints) (root : Root) (w : World) (h : History)
    (u : World) (middle : History) : Prop :=
  ∃site,Point points (canonical root) w h site u middle

noncomputable def remainder (root : Root) (children : ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoints native root w h u middle) : PrefixM Event root.Result :=
  Classical.choose (service_remainder root children (Classical.choose_spec point))

theorem remainder_run (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) :
    runPrefix root.action w h=runPrefix (remainder root children w h u middle point) u middle :=
  (Classical.choose_spec (service_remainder root children (Classical.choose_spec point))).2

theorem root_coverage (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) : RootPoints inside root w h u middle := by
  obtain ⟨site,point⟩ := point
  exact ⟨site,point.coverage children⟩

theorem root_safe (root : Root)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w)
    (point : RootPoints inside root w h u middle) : Good middle u := by
  obtain ⟨site,point⟩ := point
  exact point.safe carrierGood children before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
