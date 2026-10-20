import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitPointSource

/-! The runner's send drain and post-transmit callback use the same concrete
service source family as idle and advance. All outer runner callbacks are
therefore derived once service and dispatch bodies have their source proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.RunnerCallbacks
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def callbackPoints (service : Points.ChildPoints) (dispatch : Dispatch.Points.ChildPoints) :
    Runner.Points.ChildPoints := fun _ _ token w h u middle=>match token with
  | .sends=>service _ _ (.family .sends) w h u middle
  | .afterXmit=>AfterXmit.Points.RootPoint service w h u middle
  | .idle=>Points.RootPoints service .idle w h u middle
  | .advance=>Points.RootPoints service .advance w h u middle
  | .dispatch call=>∃site,Dispatch.Points.Point (Composition.dispatchPoints service dispatch)
      (Dispatch.Points.canonical call) w h site u middle

def runnerPoints (service : Points.ChildPoints) (dispatch : Dispatch.Points.ChildPoints) :
    Runner.Points.ChildPoints := RunnerComposition.runnerPoints service dispatch (callbackPoints service dispatch)

variable {native inside : Points.ChildPoints} {nativeDispatch insideDispatch : Dispatch.Points.ChildPoints}
  {Good : History → World → Prop}

noncomputable def otherChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    RunnerComposition.OtherChildren native inside nativeDispatch insideDispatch
      (callbackPoints native nativeDispatch) (callbackPoints inside insideDispatch) Good where
  sends := {
    remainder:=children.sends.remainder
    continuation:=children.sends.continuation
    coverage:=children.sends.coverage
    safe:=children.sends.safe }
  afterXmit := {
    remainder:=AfterXmit.Points.remainder children
    continuation:=fun _ _ _ _ point=>AfterXmit.Points.remainder_run children point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage children⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe carrierGood children before }

/-- Initialized runner callbacks conserve packets at their declared actual
service points, including the selected post-transmit branch and send drain.
Only service children and dispatch bodies remain source-contract premises;
no incoming initialized account or separate runner callback proof is assumed. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good)
    (dispatch : Composition.DispatchOther native inside nativeDispatch insideDispatch Good) :
    Runner.Points.Covered (runnerPoints native nativeDispatch) Good
      (Runner.Points.executeShape trace placeholders) [] :=
  RunnerComposition.initialized trace placeholders carrierGood children dispatch (otherChildren carrierGood children)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.RunnerCallbacks
