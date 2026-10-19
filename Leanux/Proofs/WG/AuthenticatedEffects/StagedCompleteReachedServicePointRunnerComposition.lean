import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointDispatchComposition

/-! The initialized runner and dispatch share canonical service points. The
two remaining runner children, twelve dispatch bodies and seven deeper service
families stay visible; none is filled with an empty point relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.RunnerComposition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def servicePoints (service : Points.ChildPoints) (other : Runner.Points.ChildPoints) :
    Runner.Points.ChildPoints := fun α action token w h u middle => match token with
  | .idle => Points.RootPoints service .idle w h u middle
  | .advance => Points.RootPoints service .advance w h u middle
  | token => other α action token w h u middle

def runnerPoints (service : Points.ChildPoints) (dispatch : Dispatch.Points.ChildPoints)
    (other : Runner.Points.ChildPoints) : Runner.Points.ChildPoints :=
  Dispatch.Composition.runnerPoints (Composition.dispatchPoints service dispatch)
    (servicePoints service other)

variable {native inside : Points.ChildPoints}
  {nativeDispatch insideDispatch : Dispatch.Points.ChildPoints}
  {nativeOther insideOther : Runner.Points.ChildPoints} {Good : History → World → Prop}

structure OtherChildren (native inside : Points.ChildPoints)
    (nativeDispatch insideDispatch : Dispatch.Points.ChildPoints)
    (nativeOther insideOther : Runner.Points.ChildPoints) (Good : History → World → Prop) where
  sends : Runner.Points.ChildSourceContract (runnerPoints native nativeDispatch nativeOther)
    (runnerPoints inside insideDispatch insideOther) Good .sends
  afterXmit : Runner.Points.ChildSourceContract (runnerPoints native nativeDispatch nativeOther)
    (runnerPoints inside insideDispatch insideOther) Good .afterXmit

noncomputable def runnerIdle
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (runnerPoints native nativeDispatch nativeOther)
      (runnerPoints inside insideDispatch insideOther) Good .idle where
  remainder := Points.remainder .idle children
  continuation := fun _ _ _ _ point => Points.remainder_run .idle children point
  coverage := fun _ _ _ _ point => Points.root_coverage .idle children point
  safe := fun _ _ _ _ before point => Points.root_safe .idle carrierGood children before point

noncomputable def runnerAdvance
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (runnerPoints native nativeDispatch nativeOther)
      (runnerPoints inside insideDispatch insideOther) Good .advance where
  remainder := Points.remainder .advance children
  continuation := fun _ _ _ _ point => Points.remainder_run .advance children point
  coverage := fun _ _ _ _ point => Points.root_coverage .advance children point
  safe := fun _ _ _ _ before point => Points.root_safe .advance carrierGood children before point

noncomputable def runnerOther
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeDispatch insideDispatch nativeOther insideOther Good) :
    Dispatch.Composition.OtherChildren
      (Composition.dispatchPoints native nativeDispatch) (Composition.dispatchPoints inside insideDispatch)
      (servicePoints native nativeOther) (servicePoints inside insideOther) Good where
  sends := other.sends
  afterXmit := other.afterXmit
  idle := runnerIdle carrierGood children
  advance := runnerAdvance carrierGood children

/-- Every point of the original initialized runner has the chosen security
evidence under the remaining named source contracts. Idle, advance, delivery
and dispatch are composed from their literal sources, retaining deletion's
stronger entry and requiring no incoming initialized packet account. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (service : Points.ChildContracts native inside Good)
    (dispatch : Composition.DispatchOther native inside nativeDispatch insideDispatch Good)
    (other : OtherChildren native inside nativeDispatch insideDispatch nativeOther insideOther Good) :
    Runner.Points.Covered (runnerPoints native nativeDispatch nativeOther) Good
      (Runner.Points.executeShape trace placeholders) [] :=
  Dispatch.Composition.initialized trace placeholders carrierGood
    (Composition.dispatchChildren carrierGood service dispatch) (runnerOther carrierGood service other)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.RunnerComposition
