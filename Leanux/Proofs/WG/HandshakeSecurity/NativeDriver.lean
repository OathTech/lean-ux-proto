import Leanux.Proofs.WG.TransmitSecurity.DriverOuterProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverSpecialization

/-! A neutral specialization of the shared driver. Exact event projections
to this empty journal establish native execution, without equating the
histories of two independent observers from their erased endpoints. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NativeDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity

def hooks : Driver.Hooks Empty where
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

def erase {E : Type} : E → Option Empty := fun _ => none

theorem filter_empty (h : List E) : h.filterMap (erase : E → Option Empty) = [] := by
  induction h with
  | nil => rfl
  | cons _ rest ih => exact ih

theorem state_erasure {g : WGPrefix E α} {a : WG.M α}
    (h : ErasesStatePrefix g a) : StateProjectsPrefix erase id g (liftWGPrefix a) := by
  intro w b hist
  change runWGPrefix (liftWGPrefix a) w b (hist.filterMap erase) = _
  rw [runWGPrefix_lift]
  simp only [filter_empty]
  rw [h w b hist]
  cases (a.run w).run b <;> rfl

theorem nonce_projection : Driver.HooksProjects erase Driver.nonceHooks hooks where
  deliver := projectsPrefix_lift erase _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.Projection.state_lift erase _
  handshake := fun sg sa kg ka hs hk =>
    AuthenticatedEffects.HandshakeWorker.projects erase sg sa kg ka hs hk
  fixture := ⟨id,fun _ => Driver.Projection.state_pure erase 0,
    fun _ => Driver.Projection.state_pure erase ()⟩
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift erase _
  queueSend := fun _ => Driver.Projection.state_lift erase _
  flushedSend := fun _ => Driver.Projection.state_lift erase _
  candidate := ⟨id,fun _ _ => projectsPrefix_pure erase id 0,
    fun _ => projectsPrefix_pure erase id (),
    (fun _ _ _ projected => projected)⟩
  prepare := projectsPrefix_lift erase _
  counterCheck := fun _ _ => (Driver.Projection.state_lift erase _).liftWGObserver erase id
  timer := ⟨id,fun _ _ _ _ _ => projectsPrefix_pure erase id 0,
    fun _ => projectsPrefix_pure erase id ()⟩
  selection := fun _ => Driver.Projection.state_lift erase _
  confirmation := fun _ _ => Driver.Projection.state_lift erase _
  session := fun _ => Driver.Projection.state_lift erase _
  reserve := fun kid => state_erasure (Nonce.reserveObserved_erases kid)
  allocate := fun _ => Driver.Projection.state_lift erase _
  create := fun _ _ => Driver.Projection.state_lift erase _
  front := fun _ _ _ _ => Driver.Projection.state_lift erase _
  poll := projectsPrefix_lift erase _
  encrypt := fun _ => projectsPrefix_lift erase _
  transmit := fun _ => projectsPrefix_lift erase _

theorem erases (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (Driver.executeObserved hooks trace placeholders) (Runner.executeTrace trace placeholders) := by
  intro hist
  have empty : hist = [] := by cases hist with | nil => rfl | cons x _ => cases x
  subst hist
  have projected := Driver.execute_projects nonce_projection trace placeholders []
  have output := congrArg Prod.fst projected
  simp only [List.filterMap_nil] at output
  rw [Driver.nonce_specialization] at output
  rw [Nonce.executeObserved_erases trace placeholders []] at output
  simpa only [Except.map_id,id_eq] using output

/-- A concrete exact projection to the neutral source proves native erasure
for any specialized observer, retaining both normal JSON and indexed Stop. -/
theorem projects_erases {E : Type} (g : Driver.Hooks E)
    (projected : Driver.HooksProjects erase g hooks) (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (Driver.executeObserved g trace placeholders) (Runner.executeTrace trace placeholders) := by
  intro hist
  have result := congrArg Prod.fst (Driver.execute_projects projected trace placeholders hist)
  rw [erases trace placeholders] at result
  simpa only [Except.map_id,id_eq] using result.symm

end Leanux.Proofs.WG.HandshakeSecurity.NativeDriver
