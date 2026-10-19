import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptQuietHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDisposalHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptCompletion
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! Initialized receipt integrity on the final shared Driver. This establishes
native effect witnesses and exact current-token attribution, not that every
token is authorized or that a missing/malformed context is unreachable. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

private def checkedEvent? (event : Event) : Option Event :=
  match event with
  | .cookieConsumed _ | .armed _ | .queued _ | .keepalivePrepared _ _ | .protocolSocket _ | .cookieSocket _ => some event
  | _ => none

private theorem quiet_checked (event : Event) (quiet : checkedEvent? event = none) : Unchecked event := by
  cases event <;> simp_all [checkedEvent?,Unchecked]

private theorem quiet_state_callback {body : WGPrefix Event α}
    (quiet : CallbackQuiet.StateQuiet checkedEvent? body) : Driver.StateHistorySafe Safe body :=
  CallbackQuiet.state_safe quiet (fun _ _ hi quiet => hi.quiet (fun event member => quiet_checked event (quiet event member)))

private theorem quiet_product_callback {body : PrefixM Event α}
    (quiet : CallbackQuiet.ProductQuiet checkedEvent? body) : Driver.ProductHistorySafe Safe body :=
  CallbackQuiet.product_safe quiet (fun _ _ hi quiet => hi.quiet (fun event member => quiet_checked event (quiet event member)))

private theorem old_state (body : WGPrefix Journal.Event α) :
    Driver.StateHistorySafe Safe (state body) := quiet_state Event.old old? (fun _ => True.intro) body

private theorem old_product (body : PrefixM Journal.Event α) :
    Driver.ProductHistorySafe Safe (product body) := quiet_product Event.old old? (fun _ => True.intro) body

private theorem session (pid : PeerId) : Driver.StateHistorySafe Safe (CausalJournal.session pid) :=
  receipt_quiet _ (old_state _) _ (fun _ => True.intro)

private theorem selected (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Driver.ProductHistorySafe Safe (hooks.timerSelected d j pid timer entry) := by
  intro w h hi
  exact Driver.History.product_bind
    (product_emit (.old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)) True.intro)
    (fun _ => product_enter (.timer j pid timer entry)) w h hi

private theorem keepalive_prepare (pid : PeerId) :
    Driver.StateHistorySafe Safe (CausalJournal.keepalivePrepare pid) := by
  intro w a h hi
  have observed := runWGPrefix_receiptWGObserved
    (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (Event.keepalivePrepared pid) w a h
  rw [runWGPrefix_lift] at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  unfold CausalJournal.keepalivePrepare
  rw [observed]
  cases run : ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have safe : Safe (h ++ [.keepalivePrepared pid ⟨value,w,v,a,b⟩]) := hi.emit run
    exact ⟨[.keepalivePrepared pid ⟨value,w,v,a,b⟩],rfl,safe,safe⟩

theorem hooks_safe : Driver.HooksHistorySafe Safe hooks where
  stagedRestore := fun pid packets => quiet_state_callback (CallbackQuiet.restore checkedEvent? (fun _ => rfl) pid packets)
  stagedPurge := fun _ => quiet_state Event.stagedDisposal stagedDisposal? (fun _ => True.intro) _
  peerRelease := fun _ => quiet_state Event.stagedDisposal stagedDisposal? (fun _ => True.intro) _
  deliver := by
    unfold hooks DeliverySource.observed
    exact Driver.History.product_bind (Driver.History.product_lift _) (fun w =>
      Driver.History.product_bind (product_emit (.delivery w.sent) True.intro) (fun _ =>
        Driver.History.product_lift _))
  keepalivePrepare := keepalive_prepare
  fixtureEnter := fun trigger => state_enter (.fixture trigger)
  fixtureLeave := state_leave
  handshake := handshake
  sendWorker := send_worker
  flushedSend := flushed_send
  armTimer := arm
  queueSend := queue
  candidateEnter := fun skb packet => product_enter (.candidate skb packet)
  candidateLeave := product_leave
  stackInput := fun entry _ preserves => product_scope (.stackInput entry) _ (fun _ => preserves)
  prepare := old_product _
  counterCheck := fun _ _ => old_product _
  timerSelected := selected
  timerFinished := product_leave
  selection := fun pid => quiet_state_callback (CallbackQuiet.selection checkedEvent? (fun _ => rfl) (fun _ _ => rfl) pid)
  confirmation := fun _ _ => old_state _
  session := session
  reserve := fun _ => old_state _
  allocate := fun _ => old_state _
  create := fun pid item => quiet_state_callback (CallbackQuiet.create checkedEvent? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid item)
  front := disposal_front
  poll := old_product _
  encrypt := fun item => quiet_product_callback (CallbackQuiet.encrypt checkedEvent? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) item)
  transmit := transmit

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  Driver.initialized_history hooks_safe Safe.empty trace placeholders

theorem initialized_cookie_consumed (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : CookieConsumption.Receipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.cookieConsumed receipt :: post) : receipt.Valid :=
  initialized trace placeholders pre (.cookieConsumed receipt) post position

theorem initialized_keepalive (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (receipt : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.keepalivePrepared pid receipt :: post) :
    receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid) :=
  initialized trace placeholders pre (.keepalivePrepared pid receipt) post position

theorem initialized_arm (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Arm Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.armed receipt :: post) :
    receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre :=
  initialized trace placeholders pre (.armed receipt) post position

theorem initialized_queue (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Queued Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.queued receipt :: post) :
    receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre :=
  initialized trace placeholders pre (.queued receipt) post position

theorem initialized_protocol_socket (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : ProtocolSocket.Receipt Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.protocolSocket receipt :: post) :
    receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre :=
  initialized trace placeholders pre (.protocolSocket receipt) post position

theorem initialized_cookie_socket (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : CookieSocket.Receipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.cookieSocket receipt :: post) :
    receipt.Valid := (initialized trace placeholders pre (.cookieSocket receipt) post position).1

theorem initialized_cookie_qualified (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : CookieSocket.Receipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.cookieSocket receipt :: post) :
    receipt.Valid ∧ receipt.Qualifying ∧
      (messageType receipt.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType receipt.input = MESSAGE_HANDSHAKE_RESPONSE) :=
  initialized trace placeholders pre (.cookieSocket receipt) post position

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
