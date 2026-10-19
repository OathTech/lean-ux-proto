import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
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

private theorem receipt_matching (ρ : E → Option F) (g : PrefixM E α) (t : PrefixM F α)
    (record : RunWitness α → E) (target : RunWitness α → F)
    (projects : ProjectsPrefix ρ id g t) (same : ∀ r, ρ (record r) = some (target r)) :
    ProjectsPrefix ρ id (receiptObserved g record) (receiptObserved t target) := by
  intro w h
  have base := projects w h
  change runPrefix t w (h.filterMap ρ) = _ at base
  simp only [id_eq,Prod.eta] at base
  change runPrefix (receiptObserved t target) w (h.filterMap ρ) = _
  rw [runPrefix_receiptObserved,base,runPrefix_receiptObserved]
  cases run : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out => rcases out with ⟨x,v⟩; simp [List.filterMap_append,same,Except.map]

private theorem focus_native_receipt (record : E → F) (decode : F → Option E)
    (action : WG.M α) (make : WGRunWitness α → E) :
    focusStatePrefix record decode (receiptWGObserved (liftWGPrefix action) make) =
      receiptWGObserved (liftWGPrefix action) (record ∘ make) := by
  funext w b h
  change ((runWGPrefix (receiptWGObserved (liftWGPrefix action) make) w b (h.filterMap decode)).1,
    h ++ ((runWGPrefix (receiptWGObserved (liftWGPrefix action) make) w b (h.filterMap decode)).2.drop
      (h.filterMap decode).length).map record) = _
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  change _ = runWGPrefix (receiptWGObserved (liftWGPrefix action) (record ∘ make)) w b h
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases run : (action.run w).run b with
  | error stop => simp
  | ok out => rcases out with ⟨⟨x,v⟩,c⟩; simp

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
  rw [← CookieConsumption.worker_native]
  apply CookieConsumption.worker_projects old? _ _ _ _
  · intro msg
    unfold RetirementSecurity.NestedPeerRelease.cookieObserved
    apply HandshakeSecurity.Exchange.receipt_ignored old? _ _ _ ?_ (fun _ => rfl)
    simpa only [RetirementSecurity.NestedPeerRelease.cookie_lifted,
      RetirementSecurity.NestedPeerRelease.cookie_native] using
      RetirementSecurity.NestedPeerRelease.cookie_projects old?
        (RetirementSecurity.NestedPeerRelease.observedOps_projects Event.stagedDisposal stagedDisposal? old? (fun _ => rfl)) msg
  intro mac
  apply HandshakeEffects.scopeOps_projects old? Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply HandshakeSecurity.ExchangeJoint.receive_ignored old? Event.exchange (fun _ => rfl)
  have base := ProtocolSender.receive_projects old? (Event.old ∘ Journal.Event.handshake) handshake?
    Journal.Event.handshake Journal.handshake? (fun _ => rfl) (fun _ => rfl)
    sg st kg kt hs hk mac Event.protocolSocket scope? Event.cookieSocket (fun _ => rfl) (fun _ => rfl)
  have repayment := HandshakeSecurity.StagedDisposal.Decoration.receive_projects Event.stagedDisposal
    stagedDisposal? old? (fun _ => rfl) base (fun _ => rfl)
  have accepted : HandshakeWorker.OpsProjects old? (receiveOps sg kg mac)
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake? st kt mac) :=
    {repayment with
      initiation := fun msg => RetirementSecurity.NestedPeerRelease.initiation_focused_old
        Event.stagedDisposal stagedDisposal? old? (fun _ => rfl) _
        Journal.Event.handshake Journal.handshake? (fun _ => rfl) {mac with input := msg}
      response := fun msg => RetirementSecurity.NestedPeerRelease.response_focused_old
        Event.stagedDisposal stagedDisposal? old? (fun _ => rfl) _
        Journal.Event.handshake Journal.handshake? (fun _ => rfl) {mac with input := msg}}
  have projected := HandshakeEffects.withEffects_projects old? (Event.old ∘ Journal.Event.handshake)
    Journal.Event.handshake (fun _ => rfl) _ _ effects TimerEffects.lifted accepted effects_projects
  rwa [HandshakeEffects.withEffects_neutral] at projected

theorem flushed_projects (pid : PeerId) :
    StateProjectsPrefix old? id (flushedSend pid) (Journal.hooks.flushedSend pid) :=
  SendEffects.flushed_native_projects old? Event.scope (fun _ => rfl)
    (HandshakeSecurity.ExchangeJoint.send_ignored old? Event.exchange (fun _ => rfl) _ _
      (HandshakeSecurity.StagedDisposal.Decoration.send_projects Event.stagedDisposal stagedDisposal?
        old? (fun _ => rfl)
        (ProtocolSender.send_projects old? Event.protocolSocket scope? (fun _ => rfl))
        (fun _ => rfl))) effects_projects pid

private theorem dispose_focused (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    (CompletionEffects.focused Journal.completionEvent Journal.completion?).dispose pid item key =
      focusPrefix Journal.Event.disposition Journal.disposition? (Queues.TxDisposition.dispose pid item key) := by
  simp only [CompletionEffects.focused,CompletionEffects.native,CompletionEffects.focus_composed]
  have decode : (fun e => (Journal.completion? e).bind Completion.disposition?) = Journal.disposition? := by
    funext e; cases e <;> rfl
  change focusPrefix Journal.Event.disposition _ _ = _
  rw [decode]

theorem completionLifetime_projects : LifetimeEffects.Ops.Projects old? completionLifetime
    (CompletionEffects.lifetimeBase Journal.completionEvent Journal.completion?) :=
  HandshakeSecurity.StagedDisposal.LifetimeSource.decorate_projects old?
    (Event.old ∘ Journal.completionEvent) completion? Journal.completionEvent Journal.completion?
    (fun _ => rfl) (fun _ => rfl) (fun event => by cases event <;> rfl)
    scope? Event.armed Event.queued (fun _ => rfl) (fun _ => rfl) Event.stagedDisposal (fun _ => rfl)

theorem completionOps_projects : CompletionEffects.Ops.Projects old? completionOps
    (CompletionEffects.focused Journal.completionEvent Journal.completion?) := by
  have original := CompletionEffects.observed_matching old?
    (Event.old ∘ Journal.completionEvent) completion? Journal.completionEvent Journal.completion?
    (fun _ => rfl) (fun _ => rfl) (fun event => by cases event <;> rfl)
    scope? Event.armed Event.queued (fun _ => rfl) (fun _ => rfl)
  have sent := HandshakeSecurity.StagedConservation.SendResult.decorate_projects Event.sendResult old?
    (fun _ => rfl) original
  refine {sent with dispose := ?_, fresh := ?_}
  · intro pid item key
    rw [dispose_focused]
    exact HandshakeSecurity.StagedDisposal.TxSource.dispose_observed_projects old? txEvent txEvent?
      Journal.Event.disposition Journal.disposition? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      Event.stagedDisposal (fun _ => rfl) pid item key
  · intro pid
    change ProjectsPrefix old? id (liftWGObserver (LifetimeEffects.freshWith completionLifetime pid))
      ((CompletionEffects.focused Journal.completionEvent Journal.completion?).fresh pid)
    have projected := (LifetimeEffects.fresh_projects old? completionLifetime_projects pid).liftWGObserver old? id
    simpa only [HandshakeSecurity.StagedDisposal.LifetimeSource.fresh_target
      Journal.completionEvent Journal.completion? (fun event => by cases event <;> rfl)] using projected

theorem transmit_projects (pid : PeerId) :
    ProjectsPrefix old? id (transmit pid) (Journal.transmit pid) := by
  change ProjectsPrefix old? id (transmit pid)
    (focusPrefix Journal.completionEvent Journal.completion? (Completion.step pid))
  rw [← CompletionEffects.step_focus Journal.completionEvent Journal.completion? (fun event => by cases event <;> rfl)]
  rw [← CompletionEffects.stepSource_factor]
  apply HandshakeSecurity.StagedConservation.Terminal.step_projects old? completionOps_projects _ _
    (CompletionEffects.completeScoped_projects old? Event.scope CausalSources.Cause.completion
      (fun _ => rfl) completionOps_projects) _ ?_ pid
  intro peer item head
  rw [dispose_focused]
  exact HandshakeSecurity.StagedConservation.Terminal.deadObserved_projects old? txEvent txEvent?
    Journal.Event.disposition Journal.disposition? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    Event.stagedDisposal (fun _ => rfl) Event.terminalDrop (fun _ => rfl) peer item head

theorem selection_projects (pid : PeerId) :
    StateProjectsPrefix old? id (selection pid) (Journal.selection pid) := by
  simp only [Journal.selection,HandshakeSecurity.Responder.DriverCuts.selection,focus_native_receipt]
  unfold selection
  exact HandshakeSecurity.StagedConservation.Take.selection_projects (E := Event) (F := Journal.Event)
    Event.stagingTaken old? (fun _ => rfl)
    (fun peer run => .old (.responder (.selected peer run)))
    (fun peer run => .responder (.selected peer run)) (fun _ _ => rfl) pid

theorem stagedRestore_projects (pid : PeerId) (packets : List Packet) :
    StateProjectsPrefix old? id (stagedRestore pid packets) (Journal.hooks.stagedRestore pid packets) :=
  HandshakeSecurity.StagedConservation.Restore.observed_projects Event.stagedRestored old? (fun _ => rfl) pid packets

theorem create_projects (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix old? id (create pid item) (Journal.create pid item) :=
  NativeAdapter.lower_projects old?
    (HandshakeSecurity.StagedConservation.Terminal.createObserved_projects old? txEvent txEvent?
      Journal.Event.disposition Journal.disposition? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      Event.stagedDisposal (fun _ => rfl) Event.terminalDrop (fun _ => rfl) pid item)

theorem encrypt_projects (item : Option (List SkbId)) :
    ProjectsPrefix old? id (encrypt item) (Journal.encrypt item) :=
  receipt_matching old? _ _ _ _
    (HandshakeSecurity.StagedDisposal.EncryptionSource.observed_tail_projects old?
      (Event.old ∘ Journal.Event.encrypted) (fun event => (old? event).bind Journal.encryption?)
      Journal.Event.encrypted Journal.encryption? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      Event.stagedDisposal stagedDisposal? (fun _ => rfl) item) (fun _ => rfl)

theorem front_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix old? id (front family addr packets mtu) (Journal.front family addr packets mtu) := by
  have projected := HandshakeSecurity.StagedConservation.Front.observed_projects
    (E := Event) (F := Journal.Event) Event.transmitInput Event.stagedDisposal
    stagedDisposal?
    (fun input run => .old (.routed input.family input.address input.packets input.mtu run))
    (fun input run => .routed input.family input.address input.packets input.mtu run)
    old? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) ⟨family,addr,packets,mtu⟩
  exact projected

theorem stagedPurge_projects (pid : PeerId) :
    StateProjectsPrefix old? id (stagedPurge pid) (Journal.hooks.stagedPurge pid) :=
  HandshakeSecurity.Exchange.quiet_native_projection old? _ _
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.purge_erases pid))
    (fun w => focusPrefix_other Event.stagedDisposal stagedDisposal? old? (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w))

theorem peerRelease_projects (peer : Option PeerId) :
    StateProjectsPrefix old? id (peerRelease peer) (Journal.hooks.peerRelease peer) :=
  HandshakeSecurity.StagedDisposal.Decoration.release_projects Event.stagedDisposal stagedDisposal?
    old? (fun _ => rfl) peer

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

theorem hooks_projects : Driver.HooksProjects old? hooks Journal.hooks where
  stagedRestore := stagedRestore_projects
  stagedPurge := stagedPurge_projects
  peerRelease := peerRelease_projects
  deliver := DeliverySource.observed_projects old? Event.delivery (fun _ => rfl)
  keepalivePrepare := fun _ => Journal.state_receipt_projects old? _ _ _
    (fun _ => rfl) (Driver.Projection.state_lift old? _)
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
    (fun entry _ _ projected => CausalScope.prefix_projects Event.scope (.stackInput entry) old?
      (fun _ => rfl) _ _ (fun _ => projected))⟩
  timer := ⟨(fun _ => 0),timer_projects,
    (fun token => CausalScope.leave_projects Event.scope token old? (fun _ => rfl))⟩
  prepare := product_projects _ (Appends.focus _ _ _)
  counterCheck := fun _ _ => product_projects _ ((Appends.lift _).receiptObserved)
  selection := selection_projects
  confirmation := fun _ _ => state_projects _ (StateAppends.focus _ _ _)
  session := fun pid => HandshakeSecurity.ExchangeJoint.session_ignored old? Event.exchange (fun _ => rfl)
    pid _ _ (state_projects _ (StateAppends.focus _ _ _))
  reserve := fun slot => state_projects _ (reserve_appends slot)
  allocate := fun packets => state_projects _ (allocate_appends packets)
  create := create_projects
  front := front_projects
  poll := product_projects _ ((Appends.focus _ _ _).receiptObserved)
  encrypt := encrypt_projects
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
