import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerExpandedComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointServiceComposition

/-! All seven service families share their actual timer, work, drain and
scheduler sources. The remaining scheduler and flushed-send contracts are
explicit inputs; there is no service callback assumed about its own caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Expanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def drainPoints (scheduler : Scheduler.Points.ChildPoints) (work : WorkService.Points.ChildPoints) :
    SendDrain.Points.ChildPoints := fun token w h u middle=>match token with
  | .delivery=>Points.RootPoints Points.Boundary .delivery w h u middle
  | .worker=>WorkService.Points.RootPoint work .scheduledSend w h u middle
  | .scheduler=>∃site,Scheduler.Points.Point scheduler (Scheduler.Points.scheduleShape none) w h site u middle

def points (scheduler : Scheduler.Points.ChildPoints) (work : WorkService.Points.ChildPoints) :
    Points.ChildPoints := fun _ _ token w h u middle=>match token with
  | .family (.schedule stack)=>∃site,Scheduler.Points.Point scheduler (Scheduler.Points.scheduleShape stack) w h site u middle
  | .family .sends=>SendDrain.Points.RootPoints (drainPoints scheduler work) w h u middle
  | .family .sendWorker=>WorkService.Points.RootPoint work .scheduledSend w h u middle
  | .family .clearWorker=>WorkService.Points.RootPoint work .scheduledClear w h u middle
  | .family (.timer pid timer)=>Timer.Points.RootPoint Timer.Composition.points (.callback pid timer) w h u middle
  | .family (.selected device bound pid timer entry)=>
    Timer.Points.RootPoint Timer.Composition.points (.selected device bound pid timer entry) w h u middle
  | .family (.finished token)=>Timer.Points.RootPoint Timer.Composition.points (.finished token) w h u middle

variable {nativeSchedule insideSchedule : Scheduler.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def drainChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (scheduler : Scheduler.Points.ChildContracts nativeSchedule insideSchedule Good)
    (work : WorkService.Points.ChildContracts nativeWork insideWork Good) :
    SendDrain.Points.ChildContracts (drainPoints nativeSchedule nativeWork) (drainPoints insideSchedule insideWork) Good where
  delivery := {
    remainder:=Points.deliveryRemainder
    continuation:=fun _ _ _ _ point=>Points.deliveryRemainder_run point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>carrierGood _ _ (Points.delivery_carrier before point) }
  worker := {
    remainder:=WorkService.ServiceComposition.remainder .scheduledSend work
    continuation:=fun _ _ _ _ point=>WorkService.ServiceComposition.remainder_run .scheduledSend work point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage work⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood work before.1 }
  scheduler := {
    remainder:=SchedulerComposition.remainder none scheduler
    continuation:=fun _ _ _ _ point=>SchedulerComposition.remainder_run none scheduler point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage scheduler⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe carrierGood scheduler before }

/-- Service scheduling, sends, work and timers retain their original packet
account and source continuation under the two remaining source families.
Timer callbacks use the concrete raw-repayment and keepalive construction. -/
noncomputable def children
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (scheduler : Scheduler.Points.ChildContracts nativeSchedule insideSchedule Good)
    (work : WorkService.Points.ChildContracts nativeWork insideWork Good)
    (timers : Timer.Points.ChildContracts Timer.Composition.points Timer.Composition.points Good) :
    Points.ChildContracts (points nativeSchedule nativeWork) (points insideSchedule insideWork) Good where
  schedule:=fun stack=>{
    remainder:=SchedulerComposition.remainder stack scheduler
    continuation:=fun _ _ _ _ point=>SchedulerComposition.remainder_run stack scheduler point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage scheduler⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe carrierGood scheduler before }
  sends := {
    remainder:=SendDrain.Points.remainder (drainChildren carrierGood workGood scheduler work)
    continuation:=fun _ _ _ _ point=>SendDrain.Points.remainder_run (drainChildren carrierGood workGood scheduler work) point
    coverage:=fun _ _ _ _ point=>SendDrain.Points.root_coverage (drainChildren carrierGood workGood scheduler work) point
    safe:=fun _ _ _ _ before point=>SendDrain.Points.root_safe carrierGood
      (drainChildren carrierGood workGood scheduler work) before point }
  sendWorker := {
    remainder:=WorkService.ServiceComposition.remainder .scheduledSend work
    continuation:=fun _ _ _ _ point=>WorkService.ServiceComposition.remainder_run .scheduledSend work point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage work⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood work before.1 }
  clearWorker := {
    remainder:=WorkService.ServiceComposition.remainder .scheduledClear work
    continuation:=fun _ _ _ _ point=>WorkService.ServiceComposition.remainder_run .scheduledClear work point
    coverage:=by
      intro w h u middle point
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage work⟩
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood work before.1 }
  timer:=fun pid timer=>{
    remainder:=fun _ _ _ _ point=>Classical.choose ((Classical.choose_spec point).residual timers)
    continuation:=fun _ _ _ _ point=>(Classical.choose_spec ((Classical.choose_spec point).residual timers)).run
    coverage:=fun _ _ _ _ point=>point
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood timers before.1 }
  selected:=fun device bound pid timer entry=>{
    remainder:=fun _ _ _ _ point=>Classical.choose ((Classical.choose_spec point).residual timers)
    continuation:=fun _ _ _ _ point=>(Classical.choose_spec ((Classical.choose_spec point).residual timers)).run
    coverage:=fun _ _ _ _ point=>point
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood timers before.1 }
  finished:=fun token=>{
    remainder:=fun _ _ _ _ point=>Classical.choose ((Classical.choose_spec point).residual timers)
    continuation:=fun _ _ _ _ point=>(Classical.choose_spec ((Classical.choose_spec point).residual timers)).run
    coverage:=fun _ _ _ _ point=>point
    safe:=by
      intro w h u middle before point
      obtain ⟨site,point⟩:=point
      exact point.safe workGood timers before.1 }

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Expanded
