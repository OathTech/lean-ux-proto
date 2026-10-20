import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServiceExpandedComposition

/-! Concrete timer and peer-release children reach the original initialized
runner through shared idle/advance/delivery sources. Scheduler, flushed sender,
dispatch bodies and the two remaining runner callbacks stay named contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Expanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {nativeSchedule insideSchedule : Scheduler.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints} {Good : History → World → Prop}

abbrev workPoints := WorkService.ServiceComposition.workPoints

noncomputable def concreteChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (scheduler : Scheduler.Points.ChildContracts nativeSchedule insideSchedule Good)
    (sender : ∀pid,WorkService.Points.ChildSourceContract (workPoints nativeWork) (workPoints insideWork)
      Good (.flushedSend pid)) :
    Points.ChildContracts (points nativeSchedule (workPoints nativeWork)) (points insideSchedule (workPoints insideWork)) Good :=
  children carrierGood workGood scheduler (WorkService.ServiceComposition.workChildren acceptPeer sender)
    (Timer.Composition.children workGood pendingGood acceptPeer acceptKeepalive)

/-- Initialized idle, advance and delivery callers inherit their actual
timer, work, drain and scheduling source points without incoming packet
accounts. Remaining scheduler/sender, dispatch and runner source contracts
stay visible; this theorem is not universal T2 native-cut completion. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (scheduler : Scheduler.Points.ChildContracts nativeSchedule insideSchedule Good)
    (sender : ∀pid,WorkService.Points.ChildSourceContract (workPoints nativeWork) (workPoints insideWork)
      Good (.flushedSend pid))
    (dispatch : Composition.DispatchOther (points nativeSchedule (workPoints nativeWork))
      (points insideSchedule (workPoints insideWork)) nativeDispatch insideDispatch Good)
    (other : RunnerComposition.OtherChildren (points nativeSchedule (workPoints nativeWork))
      (points insideSchedule (workPoints insideWork)) nativeDispatch insideDispatch nativeRunner insideRunner Good) :
    Runner.Points.Covered
      (RunnerComposition.runnerPoints (points nativeSchedule (workPoints nativeWork)) nativeDispatch nativeRunner)
      Good (Runner.Points.executeShape trace placeholders) [] :=
  RunnerComposition.initialized trace placeholders carrierGood
    (concreteChildren carrierGood workGood pendingGood acceptPeer acceptKeepalive scheduler sender) dispatch other

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Expanded
