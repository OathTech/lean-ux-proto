import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitReceipt

/-! The initialized routed front reaches the native post-splice world
before its receipt. That receipt is the fixed next action; its logical
account is stated after emission, on the identical native world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

theorem Caller.pre_receipt_run (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    runPrefix (liftWGObserver (Transmit.bodyPrefix caller.input)) caller.entered caller.events =
      (.ok (value,caller.updated v b),prior) := by
  rw [liftWGObserver_run,front.pre_receipt]
  rfl

def Caller.owed (caller : Caller trace placeholders operationIndex world history)
    (value : Except Int PeerId) (v : WGWorld) (b : Ambient) : WGPrefix Event Int := do
  emitStatePrefix (StagedAdmission.Front.routedEvent caller.input
    (Transmit.receipt value caller.entered.wg v caller.entered.ambient b))
  Transmit.tail value

theorem Caller.before_receipt_continuation (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (Xmit.resume trace operationIndex caller.syscall.op caller.syscall.state
        (caller.updated v b) (caller.finish (caller.owed value v b))) prior := by
  have native : runWGPrefix (Driver.transmitObserved hooks caller.input.family caller.input.address
      caller.input.packets caller.input.mtu) caller.entered.wg caller.entered.ambient caller.events =
      runWGPrefix (caller.owed value v b) v b prior := by
    rw [front.continuation]
    rfl
  have lifted : runPrefix (liftWGObserver (Driver.transmitObserved hooks caller.input.family
      caller.input.address caller.input.packets caller.input.mtu)) caller.entered caller.events =
      runPrefix (liftWGObserver (caller.owed value v b)) (caller.updated v b) prior := by
    rw [liftWGObserver_run,liftWGObserver_run]
    change ((runWGPrefix _ _ _ _).1.map _,(runWGPrefix _ _ _ _).2)=_
    rw [native]
    dsimp only [Caller.updated]
  rw [caller.original]
  apply Xmit.resume_run_eq
  unfold Caller.finish
  rw [runPrefix_bind,runPrefix_bind,lifted]

theorem Caller.receipt_account (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    ∃ ledger,
      runPrefix (liftWGObserver (Transmit.bodyPrefix caller.input)) caller.entered caller.events=
        (.ok (value,caller.updated v b),prior) ∧
      CompleteCarrier.Accounted
        (Transmit.resultHistory caller.input value caller.entered.wg v caller.entered.ambient b prior)
        ledger [] [] (caller.updated v b).wg := by
  obtain ⟨ledger,accounted⟩ := caller.front_accounted front
  exact ⟨ledger,caller.pre_receipt_run front,accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
