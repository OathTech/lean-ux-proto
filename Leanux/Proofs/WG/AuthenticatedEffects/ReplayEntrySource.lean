import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusalNative

/-! The existing shared driver projected to its actual native counter-call
receipts. Other events are discarded, not independently re-executed or joined
by erasure. The counter receipt retains its entry before later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues Packets

abbrev Event := TransportDriver.Replay

def hooks : Driver.Hooks Event where
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))
  counterCheck := TransportDriver.counter id

private theorem reserve_projects (kid : KeypairId) :
    StateProjectsPrefix Journal.replay? id (Journal.reserve kid) (liftWGPrefix (Nonce.reserveNative kid)) := by
  apply Journal.state_receipt_projects _ _ _ _ (fun _ => rfl)
  intro w
  exact projectsPrefix_focus_other Journal.Event.nonce Journal.nonce? Journal.replay? (fun _ => rfl)
    (Nonce.reserveObserved_erases kid w)

theorem hooks_projects : Driver.HooksProjects Journal.replay? Journal.hooks hooks where
  stagedRestore := fun _ _ => Driver.Projection.state_lift _ _
  stagedPurge := fun _ => Driver.Projection.state_lift _ _
  peerRelease := fun _ => Driver.Projection.state_lift _ _
  deliver := projectsPrefix_lift _ _
  keepalivePrepare := fun _ => Driver.Projection.state_lift _ _
  fixture := ⟨id,fun _ => Driver.Projection.state_pure _ 0,
    fun _ => Driver.Projection.state_pure _ ()⟩
  handshake := HandshakeWorker.observed_projects Journal.Event.handshake Journal.handshake? Journal.replay?
    (fun _ => rfl)
  flushedSend := fun _ => Driver.Projection.state_lift _ _
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift _ _
  queueSend := fun _ => Driver.Projection.state_lift _ _
  candidate := ⟨id,fun _ _ => projectsPrefix_pure _ id 0,
    fun _ => projectsPrefix_pure _ id (),fun _ _ _ projected => projected⟩
  prepare := TransportDriver.prepare_projects_other Journal.Event.rxOrigin Journal.origin? Journal.replay? (fun _ => rfl)
  counterCheck := TransportDriver.counter_projects Journal.Event.replay Journal.replay? (fun _ => rfl)
  timer := ⟨id,fun d j pid t entry => TimerDispatch.scope_projects Journal.Event.timerSelected
    d j pid t entry Journal.replay? (fun _ => rfl) id (projectsPrefix_pure _ id 0),
    fun _ => projectsPrefix_pure _ id ()⟩
  selection := fun pid w => projectsPrefix_focus_other Journal.Event.responder Journal.responder? Journal.replay?
    (fun _ => rfl) (HandshakeSecurity.Responder.DriverCuts.selection_erases pid w)
  confirmation := fun pid kid w => projectsPrefix_focus_other Journal.Event.responder Journal.responder? Journal.replay?
    (fun _ => rfl) (HandshakeSecurity.Responder.DriverCuts.confirmation_erases pid kid w)
  session := fun pid w => projectsPrefix_focus_other Journal.Event.responder Journal.responder? Journal.replay?
    (fun _ => rfl) (HandshakeSecurity.Responder.DriverCuts.session_erases pid w)
  reserve := reserve_projects
  allocate := fun _ => Journal.state_receipt_projects _ _ _ _ (fun _ => rfl) (Driver.Projection.state_lift _ _)
  front := fun _ _ _ _ => Journal.state_receipt_projects _ _ _ _ (fun _ => rfl) (Driver.Projection.state_lift _ _)
  create := fun pid item => by
    rw [show hooks.create pid item = NativeAdapter.lower (liftPrefix (liftWG (createData pid item))) from
      (NativeAdapter.lower_lift _).symm]
    exact NativeAdapter.lower_projects _
      (projectsPrefix_focus_other Journal.Event.disposition Journal.disposition? Journal.replay?
        (fun _ => rfl) (TxDisposition.create_erases pid item))
  poll := receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Journal.Event.ring Journal.ring? Journal.replay? (fun _ => rfl) TxRing.poll_erases)
  encrypt := fun item => receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Journal.Event.encrypted Journal.encryption? Journal.replay?
      (fun _ => rfl) (WorkerEncryption.tail_erases item))
  transmit := fun pid => projectsPrefix_focus_other Journal.completionEvent Journal.completion? Journal.replay?
    (fun event => by cases event <;> rfl) (Completion.step_erases pid)

theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter Journal.replay? id (Journal.execute trace placeholders)
      (Driver.executeObserved hooks trace placeholders) :=
  Driver.execute_projects hooks_projects trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
