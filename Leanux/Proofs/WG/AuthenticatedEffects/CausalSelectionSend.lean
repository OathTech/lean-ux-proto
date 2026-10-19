import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionHistory
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Actual send selection consumes the first live queue occurrence. The entry
is checked before the callback can stop; no occurrence is supplied for an
arbitrary absent-item invocation of the native flushed worker. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem emit_quiet (event : Event) (quiet : Quiet event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun h _ _ hi => hi.emit (quiet_checked event quiet h))
    (fun h _ _ hi => hi.emit (quiet_checked event quiet h))

theorem receipt_quiet (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Quiet (record r)) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind preserves.captureWGObserved (fun r =>
    Driver.History.state_bind (emit_quiet (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

theorem current_quiet (body : Context → WGPrefix Event α)
    (safe : ∀ context, Driver.StateHistorySafe Safe (body context)) :
    Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? body) := by
  intro w a h hi
  exact safe (CausalScope.current scope? h) w a h hi

theorem effects_safe : Driver.EffectsHistory Safe effects where
  step := Driver.History.state_lift
  arm := fun _ _ _ _ => current_quiet _ (fun _ =>
    receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => True.intro))
  append := fun _ => current_quiet _ (fun _ =>
    receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => True.intro))

theorem initiated (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' effect_history_step effects_safe

theorem protocol_send (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  ProtocolSocket.observed_history Safe Event.protocolSocket scope?
    (fun h args receipt hi _ => hi.emit
      (quiet_checked (.protocolSocket ⟨CausalScope.current scope? h,args,receipt⟩) True.intro h)) pid bytes

theorem cookie_send (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    Driver.StateHistorySafe Safe (CookieSocket.observed Event.cookieSocket mac msg src) :=
  CookieSocket.observed_history Safe Event.cookieSocket mac msg src
    (fun h receipt hi _ => hi.emit (quiet_checked (.cookieSocket receipt) True.intro h))

private theorem send_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head receiptWGObserved; exact receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => True.intro))
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | (driver_history_head TimerEffects.initiatedWith; exact initiated _)
    | driver_state_history_step

private theorem flushed_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head SendExchange.workerWith; exact send_body _)
    | driver_state_history_step

theorem work_scope_safe (pid : PeerId) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) (w : WGWorld) (a : Ambient) (h : List Event)
    (carrier : QueuedOccurrences.Inv Event.queued h w) (safe : Safe h)
    (present : pid ∈ QueuedOccurrences.queue w) :
    Safe (runWGPrefix (CausalSources.workScope Event.scope pid body) w a h).2 := by
  have entered := safe.emit (event := Event.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w)⟩))
    (WorkOrigin.of_carrier h w pid carrier present)
  obtain ⟨_,_,out,_⟩ := preserves w a _ entered
  rw [CausalSources.workScope_run]
  change Safe (runWGPrefix body w a _).2 at out
  cases run : runWGPrefix body w a (h ++ [Event.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w)⟩)]) with
  | mk result history =>
    rw [run] at out
    cases result with
    | error _ => exact out
    | ok _ => exact out.emit (quiet_checked (.scope (.exited h.length)) True.intro history)

abbrev Inv (h : List Event) (w : WGWorld) : Prop := Delayed.Inv h w ∧ Safe h

/-- The caller supplies actual queue membership. The selected occurrence's
strictly earlier native enqueue receipt remains in the journal on Stop. -/
theorem flushed_send (pid : PeerId) : SendCallers.SelectedSafe Inv Safe pid (flushedSend pid) := by
  intro w a h input
  obtain ⟨suffix,grown,_,output⟩ := Delayed.flushed_send pid w a h input.1.1
  have safe := work_scope_safe pid _ (flushed_body pid) w a h input.1.1.2 input.1.2 input.2
  refine ⟨suffix,grown,safe,?_⟩
  cases result : (runPrefix (StateT.run (flushedSend pid) w) a h).1 with
  | error _ => trivial
  | ok value =>
    rw [result] at output
    rcases value with ⟨⟨value,v⟩,b⟩
    exact ⟨output,safe⟩

theorem send_worker : PrefixPreserves (fun h w => Inv h w.wg) Safe (Driver.sendWorkerObserved hooks) :=
  SendCallers.one_preserves Inv Safe (fun _ _ hi => hi.2) _ flushed_send

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
