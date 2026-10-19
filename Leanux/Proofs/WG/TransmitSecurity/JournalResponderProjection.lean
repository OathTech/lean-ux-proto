import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverSource

/-! Exact current-key, session and confirmation chronology inside the shared
transmit journal. This projection preserves internal cuts on stopped prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets
namespace ResponderProjection
open HandshakeSecurity.Responder

theorem selection (pid : PeerId) :
    StateProjectsPrefix responder? id (Journal.selection pid) (DriverCuts.selection pid) := by
  have app : StateAppends (DriverCuts.selection pid) :=
    (StateAppends.lift _).receiptWGObserved _
  intro wg
  exact (app wg).project_focus Event.responder responder? (fun _ => rfl)

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    StateProjectsPrefix responder? id (Journal.confirmation pid kid) (DriverCuts.confirmation pid kid) := by
  have app : StateAppends (DriverCuts.confirmation pid kid) :=
    (StateAppends.lift _).receiptWGObserved _
  intro wg
  exact (app wg).project_focus Event.responder responder? (fun _ => rfl)

theorem session (pid : PeerId) :
    StateProjectsPrefix responder? id (Journal.session pid) (DriverCuts.session pid) := by
  have app : StateAppends (DriverCuts.session pid) :=
    (StateAppends.lift _).receiptWGObserved _
  intro wg
  exact (app wg).project_focus Event.responder responder? (fun _ => rfl)

theorem reserve (slot : KeypairId) :
    StateProjectsPrefix responder? id (Journal.reserve slot) (liftWGPrefix (Nonce.reserveNative slot)) :=
  state_receipt_projects responder? _ _ _ (fun _ => rfl)
    (fun wg => projectsPrefix_focus_other Event.nonce nonce? responder? (fun _ => rfl)
      (Nonce.reserveObserved_erases slot wg))

theorem allocate (packets : List DataPacket) :
    StateProjectsPrefix responder? id (Journal.allocate packets) (liftWGPrefix (packets.mapM newTxSkb)) :=
  state_receipt_projects responder? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift responder? _)

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix responder? id (Journal.front family addr packets mtu)
      (liftWGPrefix (txFront family addr packets mtu)) :=
  state_receipt_projects responder? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift responder? _)

theorem create (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix responder? id (Journal.create pid item) (liftWGPrefix (createData pid item)) := by
  rw [← NativeAdapter.lower_lift (createData pid item)]
  exact NativeAdapter.lower_projects responder?
    (projectsPrefix_focus_other Event.disposition disposition? responder? (fun _ => rfl) (TxDisposition.create_erases pid item))

theorem poll : ProjectsPrefix responder? id Journal.poll (liftPrefix (liftWG TxRing.pollSource)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.ring ring? responder? (fun _ => rfl) TxRing.poll_erases)

theorem encrypt (item : Option (List SkbId)) :
    ProjectsPrefix responder? id (Journal.encrypt item) (liftPrefix (RxWorkers.encryptStepTailSource item)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.encrypted encryption? responder? (fun _ => rfl) (WorkerEncryption.tail_erases item))

theorem transmit (pid : PeerId) :
    ProjectsPrefix responder? id (Journal.transmit pid) (liftPrefix (liftWG (txStep pid))) :=
  projectsPrefix_focus_other completionEvent completion? responder?
    (fun e => by cases e <;> rfl) (Completion.step_erases pid)

theorem hooks : Driver.HooksProjects responder? Journal.hooks DriverCuts.hooks where
  keepalivePrepare := fun _ => TransmitSecurity.Driver.Projection.state_lift responder? _
  fixture := ⟨id, (fun _ => Driver.Projection.state_pure responder? 0),
    (fun _ => Driver.Projection.state_pure responder? ())⟩
  handshake := AuthenticatedEffects.HandshakeWorker.observed_projects Event.handshake handshake? responder?
    (fun _ => rfl)
  flushedSend := fun _ => Driver.Projection.state_lift responder? _
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift responder? _
  queueSend := fun _ => Driver.Projection.state_lift responder? _
  candidate := ⟨id, (fun _ _ => projectsPrefix_pure responder? id 0),
    (fun _ => projectsPrefix_pure responder? id ()),
    (fun _ _ _ projected => projected)⟩
  prepare := AuthenticatedEffects.TransportDriver.prepare_projects_other Event.rxOrigin origin? responder? (fun _ => rfl)
  counterCheck := AuthenticatedEffects.TransportDriver.counter_projects_other Event.replay responder? (fun _ => rfl)
  timer := ⟨id, (fun d j pid t we =>
    AuthenticatedEffects.TimerDispatch.scope_projects Event.timerSelected d j pid t we responder?
      (fun _ => rfl) id (projectsPrefix_pure responder? id 0)),
    (fun _ => projectsPrefix_pure responder? id ())⟩
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

/-- The internal cut order is shared; equality of native endpoints alone would
not establish this chronology. Initialized authorization is proved separately. -/
theorem execute (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter responder? id (Journal.execute trace placeholders) (DriverCuts.execute trace placeholders) :=
  Driver.execute_projects hooks trace placeholders

end ResponderProjection
end Leanux.Proofs.WG.TransmitSecurity.Journal
