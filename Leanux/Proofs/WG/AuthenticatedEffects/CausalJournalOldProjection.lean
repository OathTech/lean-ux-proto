import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Exact old-journal projection for the same final Driver execution. Both
native states, returned values and every old event survive, including Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

private theorem state_projects (body : WGPrefix Journal.Event α) (appends : StateAppends body) :
    StateProjectsPrefix old? id (state body) body :=
  fun w => (appends w).project_focus Event.old old? (fun _ => rfl)

private theorem product_projects (body : PrefixM Journal.Event α) (appends : Appends body) :
    ProjectsPrefix old? id (product body) body :=
  appends.project_focus Event.old old? (fun _ => rfl)

theorem effects_projects : TimerEffects.Ops.Projects old? effects TimerEffects.lifted :=
  CausalEffects.ops_projects scope? Event.armed Event.queued old? (fun _ => rfl) (fun _ => rfl)

theorem handshake_projects (sg : PeerId → WGPrefix Event Bool)
    (st : PeerId → WGPrefix Journal.Event Bool) (kg : PeerId → WGPrefix Event Unit)
    (kt : PeerId → WGPrefix Journal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix old? id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix old? id (kg pid) (kt pid)) :
    StateProjectsPrefix old? id (handshake sg kg) (Journal.hooks.handshake st kt) := by
  change StateProjectsPrefix old? id (handshake sg kg)
    (HandshakeWorker.observed Journal.Event.handshake Journal.handshake? st kt)
  rw [HandshakeWorker.observed_factor]
  apply HandshakeEffects.worker_projects old? Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  intro mac
  exact HandshakeSecurity.ExchangeJoint.receive_ignored old? Event.exchange (fun _ => rfl) _ _
    (HandshakeEffects.effects_natural old? (Event.old ∘ Journal.Event.handshake) handshake?
      Journal.Event.handshake Journal.handshake? (fun _ => rfl) (fun _ => rfl)
      effects effects_projects sg st kg kt hs hk mac)

theorem flushed_projects (pid : PeerId) :
    StateProjectsPrefix old? id (flushedSend pid) (Journal.hooks.flushedSend pid) :=
  SendEffects.flushed_native_projects old? Event.scope (fun _ => rfl)
    (HandshakeSecurity.ExchangeJoint.send_ignored old? Event.exchange (fun _ => rfl) _ _
      (SendEffects.native_projects old?)) effects_projects pid

theorem transmit_projects (pid : PeerId) :
    ProjectsPrefix old? id (transmit pid) (Journal.transmit pid) :=
  CompletionEffects.observedStep_matching old?
    (Event.old ∘ Journal.completionEvent) completion? Journal.completionEvent Journal.completion?
    (fun _ => rfl) (fun _ => rfl) (fun event => by cases event <;> rfl)
    Event.scope scope? CausalSources.Cause.completion Event.armed Event.queued
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid

theorem timer_projects (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProjectsPrefix old? (fun _ => 0) (hooks.timerSelected d bound pid timer entry)
      (Journal.hooks.timerSelected d bound pid timer entry) := by
  intro w h
  change runPrefix (TimerDispatch.scope Journal.Event.timerSelected d bound pid timer entry (pure 0))
      w (h.filterMap old?) =
    ((runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
      d bound pid timer entry) w h).1.map (fun (_,v) => (0,v)),
      (runPrefix (CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
        d bound pid timer entry) w h).2.filterMap old?)
  simp only [CausalSources.timerEnter,TimerDispatch.scope_run]
  change (Except.ok (ε := Stop) (0,w),h.filterMap old? ++ [Journal.Event.timerSelected ⟨d,bound,pid,timer,entry,w⟩]) =
    (Except.ok (ε := Stop) (0,w),
      ((h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]) ++
        [Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)]).length,
          .timer bound pid timer entry⟩)]).filterMap old?)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,old?,List.append_nil]

private theorem reserve_appends (slot : KeypairId) : StateAppends (Journal.reserve slot) :=
  (StateAppends.focus _ _ _).receiptWGObserved _

private theorem allocate_appends (packets : List DataPacket) : StateAppends (Journal.allocate packets) :=
  (StateAppends.lift _).receiptWGObserved _

private theorem create_appends (pid : PeerId) (item : List SkbId) : StateAppends (Journal.create pid item) := by
  intro w a h
  exact Appends.focus Journal.Event.disposition Journal.disposition? (Queues.TxDisposition.create pid item)
    (NativeAdapter.world w a) h

private theorem front_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAppends (Journal.front family addr packets mtu) := (StateAppends.lift _).receiptWGObserved _

theorem hooks_projects : Driver.HooksProjects old? hooks Journal.hooks where
  fixture := ⟨(fun _ => 0),
    (fun trigger => CausalScope.enterState_projects Event.scope (.fixture trigger) old? (fun _ => rfl)),
    (fun token => CausalScope.leaveState_projects Event.scope token old? (fun _ => rfl))⟩
  handshake := handshake_projects
  flushedSend := flushed_projects
  armTimer := effects_projects.arm
  queueSend := effects_projects.append
  candidate := ⟨(fun _ => 0),
    (fun skb packet => CausalScope.enter_projects Event.scope (.candidate skb packet) old? (fun _ => rfl)),
    (fun token => CausalScope.leave_projects Event.scope token old? (fun _ => rfl)),
    (fun _ _ _ projected => projected)⟩
  timer := ⟨(fun _ => 0),timer_projects,
    (fun token => CausalScope.leave_projects Event.scope token old? (fun _ => rfl))⟩
  prepare := product_projects _ (Appends.focus _ _ _)
  counterCheck := fun _ _ => product_projects _ ((Appends.lift _).receiptObserved)
  selection := fun _ => state_projects _ (StateAppends.focus _ _ _)
  confirmation := fun _ _ => state_projects _ (StateAppends.focus _ _ _)
  session := fun pid => HandshakeSecurity.ExchangeJoint.session_ignored old? Event.exchange (fun _ => rfl)
    pid _ _ (state_projects _ (StateAppends.focus _ _ _))
  reserve := fun slot => state_projects _ (reserve_appends slot)
  allocate := fun packets => state_projects _ (allocate_appends packets)
  create := fun pid item => state_projects _ (create_appends pid item)
  front := fun family addr packets mtu => state_projects _ (front_appends family addr packets mtu)
  poll := product_projects _ ((Appends.focus _ _ _).receiptObserved)
  encrypt := fun _ => product_projects _ ((Appends.focus _ _ _).receiptObserved)
  transmit := transmit_projects

/-- Each actual syscall preserves the complete old native state and history,
not only the JSON result eventually returned by the outer runner. -/
theorem syscall_projects (call : Syscall) :
    ProjectsPrefix old? id (Driver.syscallObserved hooks call)
      (Driver.syscallObserved Journal.hooks call) :=
  Driver.syscall_projects hooks_projects call

theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter old? id (execute trace placeholders) (Journal.execute trace placeholders) :=
  Driver.execute_projects hooks_projects trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
