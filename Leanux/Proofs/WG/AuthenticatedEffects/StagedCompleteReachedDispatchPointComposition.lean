import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointRunner

/-! Compose canonical dispatch with the original initialized runner while
retaining all four service families as their actual source obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev History := List Event

def runnerPoints (dispatch : Points.ChildPoints) (other : Runner.Points.ChildPoints) : Runner.Points.ChildPoints :=
  fun α action token w h u middle => match token with
    | .dispatch call => ∃site,Points.Point dispatch (Points.canonical call) w h site u middle
    | token => other α action token w h u middle

variable {native inside : Points.ChildPoints} {nativeOther insideOther : Runner.Points.ChildPoints}
  {Good : History→World→Prop}

structure OtherChildren (native inside : Points.ChildPoints)
    (nativeOther insideOther : Runner.Points.ChildPoints) (Good : History→World→Prop) where
  sends : Runner.Points.ChildSourceContract (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good .sends
  idle : Runner.Points.ChildSourceContract (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good .idle
  afterXmit : Runner.Points.ChildSourceContract (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good .afterXmit
  advance : Runner.Points.ChildSourceContract (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good .advance

noncomputable def dispatchChild (call : Syscall)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : Points.ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good (.dispatch call) where
  remainder := Points.runnerRemainder call children
  continuation := fun _ _ _ _ point=>Points.runner_remainder call children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children (Points.canonical_framed call before)

noncomputable def runnerChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Runner.Points.ChildContracts (runnerPoints native nativeOther) (runnerPoints inside insideOther) Good where
  dispatch := fun call=>dispatchChild call carrierGood children
  sends := other.sends
  idle := other.idle
  afterXmit := other.afterXmit
  advance := other.advance

/-- Dispatch is structural in the actual initialized runner, including its
stronger deletion entry. No incoming initialized account is supplied. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Runner.Points.Covered (runnerPoints native nativeOther) Good
      (Runner.Points.executeShape trace placeholders) [] :=
  Runner.Points.initialized_covered trace placeholders carrierGood (runnerChildren carrierGood children other)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Composition
