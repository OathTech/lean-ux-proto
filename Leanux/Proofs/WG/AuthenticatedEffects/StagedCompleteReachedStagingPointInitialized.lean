import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointContract
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitInitialized

/-! Initialized routed staging uses the canonical local source and its actual
front account. Every supplied fixed source point retains the original runner
continuation; interior accounting remains at its proved concrete boundaries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open Staging.Points

theorem Caller.staging_point_continuation {remaining : WGPrefix Event Unit}
    (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      (.ok pid) v b prior)
    (point : Point (stagingShape pid) v b
      (Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior)
      leaf u c middle remaining) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (Xmit.resume trace operationIndex caller.syscall.op caller.syscall.state
        (caller.updated u c) (caller.finish (remaining >>= fun _=>Transmit.repayment pid))) middle := by
  have lifted : runPrefix (liftWGObserver (Driver.stagingObserved hooks pid)) (caller.updated v b)
      (Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior)=
      runPrefix (liftWGObserver remaining) (caller.updated u c) middle := by
    rw [liftWGObserver_run,liftWGObserver_run]
    change ((runWGPrefix _ v b _).1.map _,(runWGPrefix _ v b _).2)=_
    rw [point.residual]
    rfl
  rw [caller.front_continuation front]
  apply Xmit.resume_run_eq
  simp only [Caller.finish,Transmit.tail,liftWGObserver_bind,bind_assoc]
  rw [runPrefix_bind,runPrefix_bind,lifted]

theorem Caller.staging_source
    (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      (.ok pid) v b prior) :
    ∃ ledger,
      let events := Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior
      CompleteCarrier.Accounted events ledger [] [] v ∧
      let actual := runWGPrefix (Driver.stagingObserved hooks pid) v b events
      Execution (stagingShape pid) v b events actual.1 actual.2 := by
  obtain ⟨ledger,before⟩ := caller.front_accounted front
  exact ⟨ledger,before,Staging.Points.staging_cases pid v b _⟩

/-- Selection retains its actual taken/borrowed key receipt and same selected
cohort from initialization; the guard's native interior remains explicit. -/
theorem Caller.staging_selected
    (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      (.ok pid) v b prior)
    (selected : runWGPrefix (CausalJournal.selection pid) v b
      (Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior)=
      (.ok ((some (peer,key),u),c),middle)) :
    ∃ ledger after generation,
      let events := Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior
      Staging.Selected events ledger [] [] pid v b peer key middle u c after generation ∧
      CompleteSelected.Ready after [] [] generation pid peer events.length middle u c := by
  obtain ⟨ledger,before⟩ := caller.front_accounted front
  obtain ⟨after,generation,path,ready⟩ := selected_entry before selected
  exact ⟨ledger,after,generation,path,ready⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
