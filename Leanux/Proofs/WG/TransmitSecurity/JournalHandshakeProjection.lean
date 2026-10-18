import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeDriver
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! Actual handshake admissions and callback order inside the initialized
combined journal, including all stopped prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets
namespace HandshakeProjection
open AuthenticatedEffects

theorem selection (pid : PeerId) :
    StateProjectsPrefix handshake? id (selection pid)
      (liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? handshake? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.selection_erases pid wg)

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    StateProjectsPrefix handshake? id (confirmation pid kid) (liftWGPrefix (receivedWithKeypair pid kid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? handshake? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.confirmation_erases pid kid wg)

theorem session (pid : PeerId) :
    StateProjectsPrefix handshake? id (session pid) (liftWGPrefix (beginSession pid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? handshake? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.session_erases pid wg)

theorem reserve (slot : KeypairId) :
    StateProjectsPrefix handshake? id (Journal.reserve slot) (liftWGPrefix (Nonce.reserveNative slot)) :=
  state_receipt_projects handshake? _ _ _ (fun _ => rfl)
    (fun wg => projectsPrefix_focus_other Event.nonce nonce? handshake? (fun _ => rfl)
      (Nonce.reserveObserved_erases slot wg))

theorem allocate (packets : List DataPacket) :
    StateProjectsPrefix handshake? id (Journal.allocate packets) (liftWGPrefix (packets.mapM newTxSkb)) :=
  state_receipt_projects handshake? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift handshake? _)

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix handshake? id (Journal.front family addr packets mtu)
      (liftWGPrefix (txFront family addr packets mtu)) :=
  state_receipt_projects handshake? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift handshake? _)

theorem create (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix handshake? id (Journal.create pid item) (liftWGPrefix (createData pid item)) := by
  rw [← NativeAdapter.lower_lift (createData pid item)]
  exact NativeAdapter.lower_projects handshake?
    (projectsPrefix_focus_other Event.disposition disposition? handshake? (fun _ => rfl) (TxDisposition.create_erases pid item))

theorem poll : ProjectsPrefix handshake? id Journal.poll (liftPrefix (liftWG TxRing.pollSource)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.ring ring? handshake? (fun _ => rfl) TxRing.poll_erases)

theorem encrypt (item : Option (List SkbId)) :
    ProjectsPrefix handshake? id (Journal.encrypt item) (liftPrefix (RxWorkers.encryptStepTailSource item)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.encrypted encryption? handshake? (fun _ => rfl) (WorkerEncryption.tail_erases item))

theorem transmit (pid : PeerId) :
    ProjectsPrefix handshake? id (Journal.transmit pid) (liftPrefix (liftWG (txStep pid))) :=
  projectsPrefix_focus_other completionEvent completion? handshake?
    (fun e => by cases e <;> rfl) (Completion.step_erases pid)

theorem hooks : Driver.HooksProjects handshake? Journal.hooks HandshakeDriver.hooks where
  handshake := HandshakeWorker.observed_matching Event.handshake handshake? (fun _ => rfl)
  sendWorker := projectsPrefix_lift handshake? _
  prepare := projectsPrefix_lift handshake? _
  counterCheck := fun _ _ => (Driver.Projection.state_lift handshake? _).liftWGObserver handshake? id
  timerSelected := fun d j pid t we =>
    AuthenticatedEffects.TimerDispatch.scope_projects Event.timerSelected d j pid t we handshake?
      (fun _ => rfl) id (projectsPrefix_pure handshake? id ())
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
    ProjectsOuter handshake? id (Journal.execute trace placeholders) (Driver.executeObserved HandshakeDriver.hooks trace placeholders) :=
  Driver.execute_projects hooks trace placeholders

/-- Actual initialized runs retain a valid earlier authentication root for every
observed handshake callback, even when a later operation stops. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    HandshakeCausal.Safe ((runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap handshake?) := by
  have projected := execute trace placeholders []
  have safe := Driver.initialized_history HandshakeDriver.hooks_safe HandshakeCausal.empty_safe trace placeholders
  rw [List.filterMap_nil] at projected
  rw [projected] at safe
  exact safe

theorem callback_cause (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List HandshakeCausal.Event) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap handshake? =
      pre ++ .callback kind pid :: post) :
    ∃ r ∈ HandshakeCausal.roots pre, r.Valid ∧ r.ForPeer pid :=
  HandshakeWorker.HistorySafety.callback_cause (initialized trace placeholders) pre post kind pid position

end HandshakeProjection
end Leanux.Proofs.WG.TransmitSecurity.Journal
