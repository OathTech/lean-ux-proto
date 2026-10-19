import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionNativeFrames
import Leanux.Proofs.WG.HandshakeSecurity.NativeDriver
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeQuietNative

/-! Quiet history transport and native state transport are separate premises.
The bridge uses erasure only for the returned native state; actual all-outcome
label equality supplies history safety, including stopped prefixes. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

abbrev LabelsQuiet (g : WGPrefix Event α) :=
  ∀ initial, Driver.StateHistorySafe (fun h => Responder.DriverCuts.labels h = initial) g

theorem quiet_native {g : WGPrefix Event α} {action : WG.M α}
    (quiet : LabelsQuiet g) (erases : ErasesStatePrefix g action)
    (normal : ∀ confirmed, Preserves (Carrier confirmed) action) : Observed g := by
  intro w a h hi
  obtain ⟨suffix,appended,same,_⟩ := quiet (Responder.DriverCuts.labels h) w a h rfl
  refine ⟨suffix,appended,?_,?_⟩
  · change (Responder.DriverCuts.labels (runPrefix (g.run w) a h).2).Nodup
    rw [same]
    exact hi.2.2.distinct
  · cases outcome : (runPrefix (g.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨⟨value,v⟩,b⟩
      change Carrier (Responder.DriverCuts.labels (runPrefix (g.run w) a h).2) v
      rw [same]
      exact (hoare_iff_run_ambient _ _ _).mp (normal _) w a value v b hi
        (by
          have erased := erases w a h
          exact erased.symm.trans outcome)

theorem quiet_receipt (action : WG.M α) (make : WGRunWitness α → Event)
    (silent : ∀ r, (make r).labels = []) :
    LabelsQuiet (receiptWGObserved (liftWGPrefix action) make) := by
  intro initial w a h hi
  have equation := Responder.DriverCuts.receipt_run action make w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : (action.run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have same : Responder.DriverCuts.labels (h ++ [make ⟨value,w,v,a,b⟩]) = initial := by
      simp only [Responder.DriverCuts.labels_append,Responder.DriverCuts.labels_singleton,silent,List.append_nil,hi]
    exact ⟨[make ⟨value,w,v,a,b⟩],rfl,same,same⟩

theorem native_projection : Driver.HooksProjects NativeDriver.erase
    Responder.DriverCuts.hooks NativeDriver.hooks where
  stagedPurge := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  peerRelease := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  deliver := projectsPrefix_lift NativeDriver.erase _
  keepalivePrepare := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  fixture := ⟨id,fun _ => Driver.Projection.state_pure NativeDriver.erase 0,
    fun _ => Driver.Projection.state_pure NativeDriver.erase ()⟩
  handshake := fun sg sa kg ka hs hk =>
    AuthenticatedEffects.HandshakeWorker.projects NativeDriver.erase sg sa kg ka hs hk
  flushedSend := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift NativeDriver.erase _
  queueSend := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  candidate := ⟨id,fun _ _ => projectsPrefix_pure NativeDriver.erase id 0,
    fun _ => projectsPrefix_pure NativeDriver.erase id (),fun _ _ _ projected => projected⟩
  prepare := projectsPrefix_lift NativeDriver.erase _
  counterCheck := fun _ _ => (Driver.Projection.state_lift NativeDriver.erase _).liftWGObserver NativeDriver.erase id
  timer := ⟨id,fun _ _ _ _ _ => projectsPrefix_pure NativeDriver.erase id 0,
    fun _ => projectsPrefix_pure NativeDriver.erase id ()⟩
  selection := fun pid => NativeDriver.state_erasure (Responder.DriverCuts.selection_erases pid)
  confirmation := fun pid kid => NativeDriver.state_erasure (Responder.DriverCuts.confirmation_erases pid kid)
  session := fun pid => NativeDriver.state_erasure (Responder.DriverCuts.session_erases pid)
  reserve := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  allocate := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  create := fun _ _ => Driver.Projection.state_lift NativeDriver.erase _
  front := fun _ _ _ _ => Driver.Projection.state_lift NativeDriver.erase _
  poll := projectsPrefix_lift NativeDriver.erase _
  encrypt := fun _ => projectsPrefix_lift NativeDriver.erase _
  transmit := fun _ => projectsPrefix_lift NativeDriver.erase _

theorem native_via_nonce {g : WGPrefix Event α} {n : WGPrefix Nonce.Allocation α}
    {empty : WGPrefix Empty α} {action : WG.M α}
    (pg : StateProjectsPrefix NativeDriver.erase id g empty)
    (pn : StateProjectsPrefix NativeDriver.erase id n empty)
    (erases : ErasesStatePrefix n action) : ErasesStatePrefix g action := by
  intro w a h
  have first := congrArg Prod.fst (pg w a h)
  have second := congrArg Prod.fst (pn w a [])
  have identity : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨⟨value,world⟩,ambient⟩
    rfl
  simp only [NativeDriver.filter_empty,identity,Except.map_id] at first second
  exact first.symm.trans (second.trans (erases w a []))

/-- Used only where the source cannot invoke confirmation; the replacement
exists to reuse history-only source rules, not to claim a second execution. -/
def quietHooks : Driver.Hooks Event :=
  {Responder.DriverCuts.hooks with
    confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
    handshake := fun _ _ => liftWGPrefix receiveStep}

theorem quiet_hooks (initial : List Nat) :
    Driver.HooksHistorySafe (fun h => Responder.DriverCuts.labels h = initial) quietHooks where
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => Driver.History.state_lift _
  fixtureEnter := fun _ => Driver.History.state_pure _
  fixtureLeave := fun _ => Driver.History.state_pure _
  handshake := fun _ _ _ _ => Driver.History.state_lift _
  sendWorker := by rw [Driver.sendWorker_lift quietHooks rfl]; exact Driver.History.product_lift _
  flushedSend := fun _ => Driver.History.state_lift _
  armTimer := fun _ _ _ _ => Driver.History.state_lift _
  queueSend := fun _ => Driver.History.state_lift _
  candidateEnter := fun _ _ => Driver.History.product_pure _
  candidateLeave := fun _ => Driver.History.product_pure _
  stackInput := fun _ _ preserves => preserves
  prepare := Driver.History.product_lift _
  counterCheck := fun _ _ => (Driver.History.state_lift _).liftWGObserver
  timerSelected := fun _ _ _ _ _ => Driver.History.product_pure _
  timerFinished := fun _ => Driver.History.product_pure _
  selection := fun pid => quiet_receipt _ (.selected pid) (fun _ => rfl) initial
  confirmation := fun _ _ => Driver.History.state_lift _
  session := fun pid => quiet_receipt _ (.session pid) (fun _ => rfl) initial
  reserve := fun _ => Driver.History.state_lift _
  allocate := fun _ => Driver.History.state_lift _
  create := fun _ _ => Driver.History.state_lift _
  front := fun _ _ _ _ => Driver.History.state_lift _
  poll := Driver.History.product_lift _
  encrypt := fun _ => Driver.History.product_lift _
  transmit := fun _ => Driver.History.product_lift _

theorem staging_quiet (pid : PeerId) : LabelsQuiet (Driver.stagingObserved Responder.DriverCuts.hooks pid) :=
  fun initial => Driver.staging_history (quiet_hooks initial) pid

theorem staging_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.stagingObserved Responder.DriverCuts.hooks pid) (sendStagedPackets pid) := by
  apply native_via_nonce (Driver.staging_projects native_projection pid)
    (Driver.staging_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_staging_specialization]
  exact Nonce.stagingObserved_erases pid

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
