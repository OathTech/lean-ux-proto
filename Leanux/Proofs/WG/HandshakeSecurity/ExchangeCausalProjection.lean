import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointCookieWorker
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSenderOther
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointWorker
import Leanux.Proofs.WG.TransmitSecurity.JournalResponderProjection
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsOther

/-! Exact exchange projection of the final shared causal journal. All native
state, callback results and exchange occurrences agree on normal and stopped
runs; the larger journal also retains the old responder and transport cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity AuthenticatedEffects
open CausalJournal

private theorem native_result (rho : E → Option F) (g : PrefixM E α) (a : Leanux.M α)
    (projects : ProjectsPrefix rho id g (liftPrefix a)) : ErasesPrefix g a := by
  intro w h
  have result := congrArg Prod.fst (projects w h)
  change a.run w = (runPrefix g w h).1.map id at result
  simpa only [runStatePrefix,runPrefix,StateT.run,Except.map_id,id_eq] using result.symm

private theorem state_native (body : WGPrefix Journal.Event α) (a : WG.M α)
    (erases : ErasesStatePrefix body a) :
    StateProjectsPrefix exchange? id (state body) (liftWGPrefix a) :=
  Exchange.quiet_native_projection exchange? _ a
    (focusStatePrefix_erases Event.old old? erases)
    (fun w => focusPrefix_other Event.old old? exchange? (fun _ => rfl) (body.run w))

private theorem product_native (body : PrefixM Journal.Event α) (a : Leanux.M α)
    (erases : ErasesPrefix body a) :
    ProjectsPrefix exchange? id (product body) (liftPrefix a) :=
  projectsPrefix_focus_other Event.old old? exchange? (fun _ => rfl) erases

private theorem state_result (rho : E → Option F) (g : WGPrefix E α) (a : WG.M α)
    (projects : StateProjectsPrefix rho id g (liftWGPrefix a)) : ErasesStatePrefix g a := by
  intro w b h
  have result := congrArg Prod.fst (projects w b h)
  change (a.run w).run b = (runStatePrefix g w b h).1.map id at result
  simpa only [runStatePrefix,runPrefix,StateT.run,Except.map_id,id_eq] using result.symm

theorem effects_projects : TimerEffects.Ops.Projects exchange? effects TimerEffects.lifted :=
  CausalEffects.ops_projects scope? Event.armed Event.queued exchange? (fun _ => rfl) (fun _ => rfl)

theorem handshake_projects (sg : PeerId → WGPrefix Event Bool)
    (st : PeerId → WGPrefix Exchange.Event Bool) (kg : PeerId → WGPrefix Event Unit)
    (kt : PeerId → WGPrefix Exchange.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix exchange? id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix exchange? id (kg pid) (kt pid)) :
    StateProjectsPrefix exchange? id (handshake sg kg) (ExchangeDriver.worker st kt) := by
  apply ExchangeCookieJoint.worker_target exchange? _ _ (ExchangeDriver.receiveOps st kt) (fun _ => rfl)
  · intro msg
    exact CookieConsumption.observed_projects exchange? Event.cookieConsumed (fun _ => rfl) msg
  intro mac
  apply HandshakeEffects.scopeOps_projects exchange? Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply ExchangeJoint.receive_native exchange? Event.exchange (fun _ => rfl)
  have base := HandshakeEffects.effects_other (Event.old ∘ Journal.Event.handshake) handshake? exchange?
    (fun _ => rfl) effects effects_projects sg st kg kt hs hk mac
  have protocol := ProtocolSender.receive_other exchange?
    (Event.old ∘ Journal.Event.handshake) handshake? (fun _ => rfl)
    sg st kg kt hs hk mac Event.protocolSocket scope? Event.cookieSocket (fun _ => rfl) (fun _ => rfl)
  exact {base with send := protocol.send, cookie := protocol.cookie}

theorem flushed_projects (pid : PeerId) :
    StateProjectsPrefix exchange? id (flushedSend pid) (ExchangeDriver.flushed pid) := by
  have project := SendEffects.flushed_projects exchange? Event.scope (fun _ => rfl)
    (ExchangeJoint.send_projects exchange? Event.exchange id (fun _ => rfl)
      (ProtocolSender.sendOps Event.protocolSocket scope?) SendEffects.native
      (ProtocolSender.send_projects exchange? Event.protocolSocket scope? (fun _ => rfl))) effects_projects pid
  have neutral : SendEffects.withEffects
      (ExchangeJoint.sendOps id (SendEffects.native : SendExchange.Ops (WGPrefix Exchange.Event)))
      TimerEffects.lifted = ExchangeDriver.sendOps := by
    simp only [SendEffects.withEffects,TimerEffects.traversal_lifted,TimerEffects.initiated_lifted]
    rfl
  simpa only [neutral,flushedSend,ExchangeDriver.flushed] using project

theorem session_projects (pid : PeerId) :
    StateProjectsPrefix exchange? id (session pid) (Exchange.session pid) :=
  ExchangeJoint.session_projects exchange? Event.exchange id (fun _ => rfl) pid _ _
    (state_native _ _ (focusStatePrefix_erases Journal.Event.responder Journal.responder?
      (Responder.DriverCuts.session_erases pid)))

theorem transmit_projects (pid : PeerId) :
    ProjectsPrefix exchange? id (transmit pid) (liftPrefix (liftWG (txStep pid))) := by
  apply (transmit_history pid).project
  intro w h
  have old := congrArg Prod.fst (CausalJournal.transmit_projects pid w h)
  have native := native_result Journal.nonce? (Journal.transmit pid) _ (Journal.transmit_projects pid)
    w (h.filterMap old?)
  change (runPrefix (Journal.transmit pid) w (h.filterMap old?)).1 =
    (runPrefix (transmit pid) w h).1.map id at old
  simpa only [Except.map_id,id_eq] using old.symm.trans native

theorem timer_projects (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProjectsPrefix exchange? (fun _ => 0) (hooks.timerSelected d bound pid timer entry) (pure 0) := by
  intro w h
  change (Except.ok (ε := Stop) (0,w),h.filterMap exchange?) =
    ((runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
      d bound pid timer entry) w h).1.map (fun (_,v) => (0,v)),
      (runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
        d bound pid timer entry) w h).2.filterMap exchange?)
  simp only [CausalSources.timerEnter,TimerDispatch.scope_run]
  change (Except.ok (ε := Stop) (0,w),h.filterMap exchange?) =
    (Except.ok (ε := Stop) (0,w),
      ((h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]) ++
        [Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]).length,
          .timer bound pid timer entry⟩)]).filterMap exchange?)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,exchange?,List.append_nil]

theorem hooks_projects : Driver.HooksProjects exchange? hooks ExchangeDriver.hooks where
  deliver := DeliverySource.observed_projects exchange? Event.delivery (fun _ => rfl)
  keepalivePrepare := fun _ => Journal.state_receipt_projects exchange? _ _ _
    (fun _ => rfl) (Driver.Projection.state_lift exchange? _)
  fixture := ⟨(fun _ => 0),
    (fun trigger => CausalScope.enterState_projects Event.scope (.fixture trigger) exchange? (fun _ => rfl)),
    (fun token => CausalScope.leaveState_projects Event.scope token exchange? (fun _ => rfl))⟩
  handshake := handshake_projects
  flushedSend := flushed_projects
  armTimer := effects_projects.arm
  queueSend := effects_projects.append
  candidate := ⟨(fun _ => 0),
    (fun skb packet => CausalScope.enter_projects Event.scope (.candidate skb packet) exchange? (fun _ => rfl)),
    (fun token => CausalScope.leave_projects Event.scope token exchange? (fun _ => rfl)),
    (fun entry _ _ projected => CausalScope.prefix_projects Event.scope (.stackInput entry) exchange?
      (fun _ => rfl) _ _ (fun _ => projected))⟩
  timer := ⟨(fun _ => 0),timer_projects,
    (fun token => CausalScope.leave_projects Event.scope token exchange? (fun _ => rfl))⟩
  prepare := product_native _ _ (TransportDriver.prepare_erases _ _)
  counterCheck := fun skb packet => product_native _ _ (TransportDriver.counter_erases _ skb packet)
  selection := fun pid => state_native _ _ (focusStatePrefix_erases Journal.Event.responder Journal.responder?
    (Responder.DriverCuts.selection_erases pid))
  confirmation := fun pid kid => state_native _ _ (focusStatePrefix_erases Journal.Event.responder Journal.responder?
    (Responder.DriverCuts.confirmation_erases pid kid))
  session := session_projects
  reserve := fun slot => state_native _ _ (state_result Journal.responder? _ _ (Journal.ResponderProjection.reserve slot))
  allocate := fun packets => state_native _ _ (state_result Journal.responder? _ _ (Journal.ResponderProjection.allocate packets))
  create := fun pid item => state_native _ _ (state_result Journal.responder? _ _ (Journal.ResponderProjection.create pid item))
  front := fun family addr packets mtu => state_native _ _ (state_result Journal.responder? _ _
    (Journal.ResponderProjection.front family addr packets mtu))
  poll := product_native _ _ (native_result Journal.responder? _ _ Journal.ResponderProjection.poll)
  encrypt := fun item => product_native _ _ (native_result Journal.responder? _ _ (Journal.ResponderProjection.encrypt item))
  transmit := transmit_projects

/-- The complete initialized exchange history is an exact ordered projection
of the final source journal, including receipts before an internal Stop. -/
theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter exchange? id (execute trace placeholders) (ExchangeDriver.execute trace placeholders) :=
  Driver.execute_projects hooks_projects trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
