import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionSource

/-! Exact responder projection at the final exchange-session receipt. The old
session marker is discarded and its same-call outer receipt is retained, so
initialized C1 slot guards apply at that receipt without an event-pairing
assumption or a second independently erased execution. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity AuthenticatedEffects
open CausalJournal Origins.HandshakeSources

private theorem effects_projects : TimerEffects.Ops.Projects cut? effects TimerEffects.lifted :=
  CausalEffects.ops_projects scope? Event.armed Event.queued cut? (fun _ => rfl) (fun _ => rfl)

private theorem receive_projects (base : Ops (WGPrefix Event))
    (sg : PeerId → WGPrefix Cut Bool) (kg : PeerId → WGPrefix Cut Unit)
    (project : HandshakeWorker.OpsProjects cut? base (HandshakeWorker.ops sg kg)) :
    HandshakeWorker.OpsProjects cut? (ExchangeJoint.receiveOps Event.exchange base)
      (HandshakeWorker.ops sg kg) :=
  {project with
    create := fun pid => Exchange.receipt_ignored cut? _ _ _ (project.create pid) (fun _ => rfl)
    initiation := fun msg => Exchange.receipt_ignored cut? _ _ _ (project.initiation msg) (fun _ => rfl)
    response := fun msg => Exchange.receipt_ignored cut? _ _ _ (project.response msg) (fun _ => rfl)}

theorem handshake_projects (sg : PeerId → WGPrefix Event Bool)
    (st : PeerId → WGPrefix Cut Bool) (kg : PeerId → WGPrefix Event Unit)
    (kt : PeerId → WGPrefix Cut Unit)
    (hs : ∀ pid, StateProjectsPrefix cut? id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix cut? id (kg pid) (kt pid)) :
    StateProjectsPrefix cut? id (handshake sg kg) (Responder.DriverCuts.hooks.handshake st kt) := by
  apply ExchangeCookieJoint.worker_target cut? _ _ (HandshakeWorker.ops st kt) (fun _ => rfl)
  · intro msg
    exact CookieConsumption.observed_projects cut? Event.cookieConsumed (fun _ => rfl) msg
  intro mac
  apply HandshakeEffects.scopeOps_projects cut? Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply receive_projects
  have base := HandshakeEffects.effects_other (Event.old ∘ Journal.Event.handshake) handshake? cut?
    (fun _ => rfl) effects effects_projects sg st kg kt hs hk mac
  have protocol := ProtocolSender.receive_other cut?
    (Event.old ∘ Journal.Event.handshake) handshake? (fun _ => rfl)
    sg st kg kt hs hk mac Event.protocolSocket scope? Event.cookieSocket (fun _ => rfl) (fun _ => rfl)
  exact {base with send := protocol.send, cookie := protocol.cookie}

theorem flushed_projects (pid : PeerId) :
    StateProjectsPrefix cut? id (flushedSend pid) (Responder.DriverCuts.hooks.flushedSend pid) := by
  apply SendEffects.flushed_native_projects cut? Event.scope (fun _ => rfl) ?_ effects_projects pid
  refine {ProtocolSender.send_projects cut? Event.protocolSocket scope? (fun _ => rfl) with create := ?_}
  intro actor
  exact Exchange.receipt_ignored cut? _ _ _ (Driver.Projection.state_lift cut? _) (fun _ => rfl)

theorem transmit_projects (pid : PeerId) :
    ProjectsPrefix cut? id (transmit pid) (liftPrefix (liftWG (txStep pid))) := by
  apply HistoryFrame.project
  · exact ExchangeCausal.transmit_history_of_quiet cut? (fun e => by cases e <;> rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid
  · intro w h
    have old := congrArg Prod.fst (CausalJournal.transmit_projects pid w h)
    have native := congrArg Prod.fst (Journal.ResponderProjection.transmit pid w (h.filterMap old?))
    change (runPrefix (Journal.transmit pid) w (h.filterMap old?)).1 =
      (runPrefix (transmit pid) w h).1.map id at old
    change (liftWG (txStep pid)).run w =
      (runPrefix (Journal.transmit pid) w (h.filterMap old?)).1.map id at native
    simp only [Except.map_id,id_eq] at old native
    exact old.symm.trans native.symm

private theorem timer_projects (d : Device) (bound : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry) :
    ProjectsPrefix cut? (fun _ => 0) (hooks.timerSelected d bound pid timer entry) (pure 0) := by
  intro w h
  change (Except.ok (ε := Stop) (0,w),h.filterMap cut?) =
    ((runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
      d bound pid timer entry) w h).1.map (fun (_,v) => (0,v)),
      (runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
        d bound pid timer entry) w h).2.filterMap cut?)
  simp only [CausalSources.timerEnter,TimerDispatch.scope_run]
  change (Except.ok (ε := Stop) (0,w),h.filterMap cut?) =
    (Except.ok (ε := Stop) (0,w),
      ((h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]) ++
        [Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]).length,
          .timer bound pid timer entry⟩)]).filterMap cut?)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,cut?,List.append_nil]

private theorem create_appends (pid : PeerId) (item : List SkbId) : StateAppends (Journal.create pid item) := by
  intro w a h
  exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid item)
    (NativeAdapter.world w a) h

theorem hooks_projects : Driver.HooksProjects cut? hooks Responder.DriverCuts.hooks where
  deliver := DeliverySource.observed_projects cut? Event.delivery (fun _ => rfl)
  keepalivePrepare := fun _ => Journal.state_receipt_projects cut? _ _ _
    (fun _ => rfl) (Driver.Projection.state_lift cut? _)
  fixture := ⟨(fun _ => 0),
    (fun trigger => CausalScope.enterState_projects Event.scope (.fixture trigger) cut? (fun _ => rfl)),
    (fun token => CausalScope.leaveState_projects Event.scope token cut? (fun _ => rfl))⟩
  handshake := handshake_projects
  flushedSend := flushed_projects
  armTimer := effects_projects.arm
  queueSend := effects_projects.append
  candidate := ⟨(fun _ => 0),
    (fun skb packet => CausalScope.enter_projects Event.scope (.candidate skb packet) cut? (fun _ => rfl)),
    (fun token => CausalScope.leave_projects Event.scope token cut? (fun _ => rfl)),
    (fun entry _ _ projected => CausalScope.prefix_projects Event.scope (.stackInput entry) cut?
      (fun _ => rfl) _ _ (fun _ => projected))⟩
  timer := ⟨(fun _ => 0),timer_projects,
    (fun token => CausalScope.leave_projects Event.scope token cut? (fun _ => rfl))⟩
  prepare := product_native _ _ (Appends.focus _ _ _) Journal.ResponderProjection.hooks.prepare
  counterCheck := by
    intro skb packet
    change ProjectsPrefix cut? id
      (product (TransportDriver.counter Journal.Event.replay skb packet))
      (liftPrefix (liftWG (counterValidate packet.keypair packet.nonce)))
    exact product_native _ _ ((Appends.lift _).receiptObserved)
      (TransportDriver.counter_projects_other Journal.Event.replay Journal.responder?
        (fun _ => rfl) skb packet)
  selection := selection_projects
  confirmation := confirmation_projects
  session := session_projects
  reserve := fun slot => state_native _ _ ((StateAppends.focus _ _ _).receiptWGObserved _)
    (Journal.ResponderProjection.reserve slot)
  allocate := fun packets => state_native _ _ ((StateAppends.lift _).receiptWGObserved _)
    (Journal.ResponderProjection.allocate packets)
  create := fun pid item => state_native _ _ (create_appends pid item) (Journal.ResponderProjection.create pid item)
  front := fun family addr packets mtu => state_native _ _ ((StateAppends.lift _).receiptWGObserved _)
    (Journal.ResponderProjection.front family addr packets mtu)
  poll := product_native _ _ ((Appends.focus _ _ _).receiptObserved) Journal.ResponderProjection.poll
  encrypt := fun item => product_native _ _ ((Appends.focus _ _ _).receiptObserved) (Journal.ResponderProjection.encrypt item)
  transmit := transmit_projects

theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter cut? id (execute trace placeholders) (Responder.DriverCuts.execute trace placeholders) :=
  Driver.execute_projects hooks_projects trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
