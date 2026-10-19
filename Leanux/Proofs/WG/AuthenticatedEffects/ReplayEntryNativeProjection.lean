import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntrySource
import Leanux.Proofs.WG.HandshakeSecurity.NativeDriver

/-! Native-result projections for the counter-only source. These equations
are used only for native state frames; all counter-entry history is proved
on the actual counter observer and never inferred from result erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open HandshakeSecurity

theorem native_projects : Driver.HooksProjects NativeDriver.erase hooks NativeDriver.hooks where
  stagedPurge := fun _ => Driver.Projection.state_lift _ _
  peerRelease := fun _ => Driver.Projection.state_lift _ _
  deliver := projectsPrefix_lift _ _
  keepalivePrepare := fun _ => Driver.Projection.state_lift _ _
  fixture := ⟨id,fun _ => Driver.Projection.state_pure _ 0,
    fun _ => Driver.Projection.state_pure _ ()⟩
  handshake := HandshakeWorker.projects _
  flushedSend := fun _ => Driver.Projection.state_lift _ _
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift _ _
  queueSend := fun _ => Driver.Projection.state_lift _ _
  candidate := ⟨id,fun _ _ => projectsPrefix_pure _ id 0,
    fun _ => projectsPrefix_pure _ id (),fun _ _ _ projected => projected⟩
  prepare := projectsPrefix_lift _ _
  counterCheck := fun skb pkt => by
    change ProjectsPrefix _ id (TransportDriver.counter id skb pkt)
      (liftPrefix (liftWG (counterValidate pkt.keypair pkt.nonce)))
    exact TransportDriver.counter_projects_other id _ (fun _ => rfl) skb pkt
  timer := ⟨id,fun _ _ _ _ _ => projectsPrefix_pure _ id 0,
    fun _ => projectsPrefix_pure _ id ()⟩
  selection := fun _ => Driver.Projection.state_lift _ _
  confirmation := fun _ _ => Driver.Projection.state_lift _ _
  session := fun _ => Driver.Projection.state_lift _ _
  reserve := fun _ => Driver.Projection.state_lift _ _
  allocate := fun _ => Driver.Projection.state_lift _ _
  create := fun _ _ => Driver.Projection.state_lift _ _
  front := fun _ _ _ _ => Driver.Projection.state_lift _ _
  poll := projectsPrefix_lift _ _
  encrypt := fun _ => projectsPrefix_lift _ _
  transmit := fun _ => projectsPrefix_lift _ _

theorem state_native_result {body : WGPrefix Event α} {neutral : WGPrefix Empty α}
    {nonce : WGPrefix Nonce.Allocation α} {native : WG.M α}
    (source : StateProjectsPrefix NativeDriver.erase id body neutral)
    (older : StateProjectsPrefix NativeDriver.erase id nonce neutral)
    (erases : ErasesStatePrefix nonce native) : ErasesStatePrefix body native := by
  intro w a history
  have first := congrArg Prod.fst (source w a history)
  have second := congrArg Prod.fst (older w a [])
  simp only [NativeDriver.filter_empty,List.filterMap_nil,Prod.map_id,id_eq,Prod.eta] at first second
  have map_identity {ε β : Type} (x : Except ε β) : Except.map (fun y => y) x = x := by
    cases x <;> rfl
  simp only [map_identity] at first second
  exact first.symm.trans (second.trans (erases w a []))

theorem product_native_result {body : PrefixM Event α} {neutral : PrefixM Empty α}
    {nonce : PrefixM Nonce.Allocation α} {native : Leanux.M α}
    (source : ProjectsPrefix NativeDriver.erase id body neutral)
    (older : ProjectsPrefix NativeDriver.erase id nonce neutral)
    (erases : ErasesPrefix nonce native) : ErasesPrefix body native := by
  intro w history
  have first := congrArg Prod.fst (source w history)
  have second := congrArg Prod.fst (older w [])
  simp only [NativeDriver.filter_empty,List.filterMap_nil,id_eq,Prod.eta] at first second
  have map_identity {ε β : Type} (x : Except ε β) : Except.map (fun y => y) x = x := by
    cases x <;> rfl
  simp only [map_identity] at first second
  exact first.symm.trans (second.trans (erases w []))

theorem staging_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.stagingObserved hooks pid) (sendStagedPackets pid) := by
  apply state_native_result (Driver.staging_projects native_projects pid)
    (Driver.staging_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_staging_specialization]
  exact Nonce.stagingObserved_erases pid

theorem keepalive_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.keepaliveObserved hooks pid) (sendKeepalive pid) := by
  apply state_native_result (Driver.keepalive_projects native_projects pid)
    (Driver.keepalive_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_keepaliveObserved_eq]
  exact Nonce.keepaliveObserved_erases pid

theorem handshake_erases :
    ErasesStatePrefix (Driver.handshakeObserved hooks) receiveStep := by
  apply state_native_result (Driver.handshake_projects native_projects)
    (Driver.handshake_projects NativeDriver.nonce_projection)
  rw [Driver.nonce_handshakeObserved_eq]
  exact Nonce.Handshake.erases

theorem consume_erases (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    ErasesStatePrefix (Driver.consumeObserved hooks pid packet endpoint) (consumeDataDone pid packet endpoint) := by
  apply state_native_result (Driver.consume_projects native_projects pid packet endpoint)
    (Driver.consume_projects NativeDriver.nonce_projection pid packet endpoint)
  rw [Driver.nonce_consumeObserved_eq]
  exact Nonce.consumeObserved_erases pid packet endpoint

theorem stack_erases (bytes : List UInt8) :
    ErasesPrefix (Driver.stackObserved hooks bytes) (Env.Stack.receive bytes) := by
  apply product_native_result (Driver.stack_projects native_projects bytes)
    (Driver.stack_projects NativeDriver.nonce_projection bytes)
  rw [Driver.nonce_stackObserved_eq]
  exact Nonce.stackObserved_erases bytes

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
