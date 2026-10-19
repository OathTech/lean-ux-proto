import Leanux.Proofs.WG.TransmitSecurity.JournalSource
import Leanux.Proofs.WG.TransmitSecurity.DriverSpecialization

/-! Exact reservation projection of the combined execution. This equality
links internal occurrence order; it is stronger than native result erasure. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets
set_option pp.structureInstances false

theorem state_receipt_projects {E F α : Type} (ρ : E → Option F)
    (g : WGPrefix E α) (a : WGPrefix F α) (receipt : WGRunWitness α → E)
    (hr : ∀ r, ρ (receipt r) = none) (hp : StateProjectsPrefix ρ id g a) :
    StateProjectsPrefix ρ id (receiptWGObserved g receipt) a := by
  intro wg ambient hist
  have he := hp wg ambient hist
  change runWGPrefix a wg ambient (hist.filterMap ρ) = _ at he ⊢
  rw [he]
  change _ = ((runWGPrefix (receiptWGObserved g receipt) wg ambient hist).1.map _,
    (runWGPrefix (receiptWGObserved g receipt) wg ambient hist).2.filterMap ρ)
  rw [runWGPrefix_receiptWGObserved]
  cases out : runWGPrefix g wg ambient hist with
  | mk result journal =>
    simp only [runWGPrefix,runStatePrefix] at out
    rw [out]
    cases result with
    | error e => rfl
    | ok value =>
      rcases value with ⟨⟨x,w⟩,b⟩
      simp [List.filterMap_append,hr]

private theorem reserve_appends (slot : KeypairId) : StateAppends (Nonce.reserveObserved slot) := by
  unfold Nonce.reserveObserved
  apply StateAppends.bind (StateAppends.lift _)
  intro k
  apply StateAppends.bind (StateAppends.lift _)
  intro _
  apply StateAppends.bind
  · intro wg ambient hist
    exact ⟨[Nonce.allocation (Nonce.cell k)],rfl⟩
  · intro _
    exact StateAppends.pure _

theorem reserve_projects (slot : KeypairId) :
    StateProjectsPrefix nonce? id (reserve slot) (Nonce.reserveObserved slot) := by
  apply state_receipt_projects nonce? _ _ _ (fun _ => rfl)
  intro wg
  exact (reserve_appends slot wg).project_focus Event.nonce nonce? (fun _ => rfl)

theorem allocate_projects (packets : List DataPacket) :
    StateProjectsPrefix nonce? id (allocate packets) (liftWGPrefix (packets.mapM newTxSkb)) :=
  state_receipt_projects nonce? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift nonce? _)

theorem front_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix nonce? id (front family addr packets mtu)
      (liftWGPrefix (txFront family addr packets mtu)) :=
  state_receipt_projects nonce? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift nonce? _)

theorem create_projects (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix nonce? id (create pid item) (liftWGPrefix (createData pid item)) := by
  rw [← NativeAdapter.lower_lift (createData pid item)]
  exact NativeAdapter.lower_projects nonce?
    (projectsPrefix_focus_other Event.disposition disposition? nonce? (fun _ => rfl) (TxDisposition.create_erases pid item))

theorem poll_projects : ProjectsPrefix nonce? id poll (liftPrefix (liftWG TxRing.pollSource)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.ring ring? nonce? (fun _ => rfl) TxRing.poll_erases)

theorem encrypt_projects (item : Option (List SkbId)) :
    ProjectsPrefix nonce? id (encrypt item) (liftPrefix (RxWorkers.encryptStepTailSource item)) :=
  receiptObserved_projects (fun _ => rfl)
    (projectsPrefix_focus_other Event.encrypted encryption? nonce? (fun _ => rfl) (WorkerEncryption.tail_erases item))

theorem transmit_projects (pid : PeerId) :
    ProjectsPrefix nonce? id (transmit pid) (liftPrefix (liftWG (txStep pid))) :=
  projectsPrefix_focus_other completionEvent completion? nonce?
    (fun e => by cases e <;> rfl) (Completion.step_erases pid)

theorem selection_projects (pid : PeerId) :
    StateProjectsPrefix nonce? id (selection pid)
      (liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? nonce? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.selection_erases pid wg)

theorem confirmation_projects (pid : PeerId) (kid : KeypairId) :
    StateProjectsPrefix nonce? id (confirmation pid kid) (liftWGPrefix (receivedWithKeypair pid kid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? nonce? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.confirmation_erases pid kid wg)

theorem session_projects (pid : PeerId) :
    StateProjectsPrefix nonce? id (session pid) (liftWGPrefix (beginSession pid)) :=
  fun wg => projectsPrefix_focus_other Event.responder responder? nonce? (fun _ => rfl)
    (HandshakeSecurity.Responder.DriverCuts.session_erases pid wg)

theorem hooks_projects : Driver.HooksProjects nonce? hooks Driver.nonceHooks where
  handshake := AuthenticatedEffects.HandshakeWorker.observed_projects Event.handshake handshake? nonce?
    (fun _ => rfl)
  flushedSend := fun _ => Driver.Projection.state_lift nonce? _
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift nonce? _
  queueSend := fun _ => Driver.Projection.state_lift nonce? _
  candidate := ⟨id, (fun _ _ => projectsPrefix_pure nonce? id 0),
    (fun _ => projectsPrefix_pure nonce? id ())⟩
  prepare := AuthenticatedEffects.TransportDriver.prepare_projects_other Event.rxOrigin origin? nonce? (fun _ => rfl)
  counterCheck := AuthenticatedEffects.TransportDriver.counter_projects_other Event.replay nonce? (fun _ => rfl)
  timerSelected := fun d j pid t we =>
    AuthenticatedEffects.TimerDispatch.scope_projects Event.timerSelected d j pid t we nonce?
      (fun _ => rfl) id (projectsPrefix_pure nonce? id ())
  selection := selection_projects
  confirmation := confirmation_projects
  session := session_projects
  reserve := reserve_projects
  allocate := allocate_projects
  create := create_projects
  front := front_projects
  poll := poll_projects
  encrypt := encrypt_projects
  transmit := transmit_projects

theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter nonce? id (execute trace placeholders) (Nonce.executeObserved trace placeholders) := by
  rw [← Driver.nonce_specialization]
  exact Driver.execute_projects hooks_projects trace placeholders

/-- All allocations in this combined chronology are unique, even when the
execution stops after a reservation or during a later packet worker. -/
theorem initialized_reservations (trace : Runner.Trace) (placeholders : Bool) :
    List.Nodup ((runPrefixOuter (execute trace placeholders) []).2.filterMap nonce?) := by
  have hp := execute_projects trace placeholders []
  have hn := Nonce.initialized_safe trace placeholders
  rw [List.filterMap_nil] at hp
  rw [hp] at hn
  exact hn

theorem execute_erases (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (execute trace placeholders) (Runner.executeTrace trace placeholders) := by
  intro hist
  have hp := congrArg Prod.fst (execute_projects trace placeholders hist)
  have he := Nonce.executeObserved_erases trace placeholders (hist.filterMap nonce?)
  simpa only [Except.map_id,id_eq] using hp.symm.trans he

end Leanux.Proofs.WG.TransmitSecurity.Journal
