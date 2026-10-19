import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionContracts
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Actual timer/work receipts are valid native executions and retain the
current lexical token at their own journal position. This invariant does not
classify missing/malformed tokens as authorized. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def Checked (pre : List Event) : Event → Prop
  | .cookieConsumed receipt => receipt.Valid
  | .keepalivePrepared pid receipt => receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid)
  | .armed receipt => receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre
  | .queued receipt => receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre
  | .protocolSocket receipt => receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre
  | .cookieSocket receipt => receipt.Valid ∧ receipt.Qualifying ∧
      (messageType receipt.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType receipt.input = MESSAGE_HANDSHAKE_RESPONSE)
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Unchecked : Event → Prop
  | .cookieConsumed _ | .armed _ | .queued _ | .keepalivePrepared _ _ | .protocolSocket _ | .cookieSocket _ => False
  | _ => True

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (hi : Safe h)
    (checked : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix hi checked

theorem unchecked_checked (event : Event) (quiet : Unchecked event) (pre : List Event) : Checked pre event := by
  cases event <;> first | exact quiet.elim | trivial

theorem Safe.quiet (hi : Safe h) (quiet : ∀ event ∈ suffix, Unchecked event) : Safe (h ++ suffix) := by
  apply hi.append
  intro pre event post position
  apply unchecked_checked event
  apply quiet event
  rw [position]
  simp

theorem Safe.emit (hi : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply hi.append
  intro pre entry post position
  cases pre with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

theorem quiet_state (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Unchecked (encode event)) (body : WGPrefix F α) :
    Driver.StateHistorySafe Safe (focusStatePrefix encode decode body) := by
  intro w a h hi
  let suffix := ((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix encode decode body) w) a h).1 <;> trivial

theorem quiet_product (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Unchecked (encode event)) (body : PrefixM F α) :
    Driver.ProductHistorySafe Safe (focusPrefix encode decode body) := by
  intro w h hi
  let suffix := ((runPrefix body w (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (focusPrefix encode decode body) w h).1 <;> trivial

theorem emit_quiet (event : Event) (quiet : Unchecked event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun h _ _ hi => hi.emit (unchecked_checked event quiet h))
    (fun h _ _ hi => hi.emit (unchecked_checked event quiet h))

theorem receipt_quiet (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Unchecked (record r)) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind preserves.captureWGObserved (fun r =>
    Driver.History.state_bind (emit_quiet (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

theorem state_scope (cause : Cause) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) :
    Driver.StateHistorySafe Safe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ hi => hi)
    (fun event h _ _ hi => hi.emit (unchecked_checked (.scope event) True.intro h)) preserves

theorem state_enter (cause : Cause) :
    Driver.StateHistorySafe Safe (CausalScope.enterState Event.scope cause) :=
  CausalScope.enterState_preserves Event.scope cause (fun _ _ _ hi => hi)
    (fun event h _ _ hi => hi.emit (unchecked_checked (.scope event) True.intro h))

theorem state_leave (token : Nat) :
    Driver.StateHistorySafe Safe (CausalScope.leaveState Event.scope token) :=
  emit_quiet _ True.intro

theorem product_emit (event : Event) (quiet : Unchecked event) :
    Driver.ProductHistorySafe Safe (emitPrefix event) := by
  intro w h hi
  have good := hi.emit (unchecked_checked event quiet h)
  exact ⟨[event],rfl,good,good⟩

theorem product_enter (cause : Cause) :
    Driver.ProductHistorySafe Safe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have good := hi.emit (unchecked_checked (.scope (.entered ⟨h.length,cause⟩)) True.intro h)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem product_leave (token : Nat) :
    Driver.ProductHistorySafe Safe (CausalScope.leavePrefix Event.scope token) :=
  product_emit _ True.intro

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (preserves : ∀ token, Driver.ProductHistorySafe Safe (body token)) :
    Driver.ProductHistorySafe Safe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact Driver.History.product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)) True.intro)
    (fun _ => Driver.History.product_bind (preserves ⟨h.length,cause⟩) (fun result =>
      Driver.History.product_bind (product_leave h.length) (fun _ => Driver.History.product_pure result))) w h hi

/-- The native callback runs once. Its own old receipts may precede the new
receipt, but its scope frame fixes the exact current-token value there. -/
theorem recorded (body : WGPrefix Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (preserves : Driver.StateHistorySafe Safe body)
    (frame : StateHistoryFrame scope? body) (record : Context → WGRunWitness α → Event)
    (checked : ∀ h receipt, receipt.Valid native → Checked h (record (CausalScope.current scope? h) receipt)) :
    Driver.StateHistorySafe Safe
      (CausalEffects.atCurrent scope? fun context => receiptWGObserved body (record context)) := by
  intro w a h hi
  obtain ⟨suffix,grown,safe,_⟩ := preserves w a h hi
  have observed := CausalEffects.atCurrent_run scope?
    (fun context => receiptWGObserved body (record context)) w a h
  rw [runWGPrefix_receiptWGObserved] at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  change (runPrefix (body.run w) a h).2 = h ++ suffix at grown
  change Safe (runPrefix (body.run w) a h).2 at safe
  cases run : runWGPrefix body w a h with
  | mk result history =>
    simp only [runWGPrefix,runStatePrefix] at run
    rw [run] at grown safe ⊢
    cases result with
    | error stop => exact ⟨suffix,grown,safe,True.intro⟩
    | ok result =>
      rcases result with ⟨⟨value,v⟩,b⟩
      let receipt : WGRunWitness α := ⟨value,w,v,a,b⟩
      have nativeRun : receipt.Valid native := (erases w a h).symm.trans (congrArg Prod.fst run)
      have same := frame w a h
      change (runWGPrefix body w a h).2.filterMap scope? = h.filterMap scope? at same
      simp only [runWGPrefix,runStatePrefix] at same
      rw [run] at same
      have current : CausalScope.current scope? history = CausalScope.current scope? h :=
        congrArg (fun events => (CausalScope.stack events).map List.head?) same
      have now := checked history receipt nativeRun
      rw [current] at now
      have good := safe.emit now
      exact ⟨suffix ++ [record (CausalScope.current scope? h) receipt],by
        change history = h ++ suffix at grown
        change history ++ [record (CausalScope.current scope? h) receipt] = _
        rw [grown,List.append_assoc],good,good⟩

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Driver.StateHistorySafe Safe (effects.arm pid timer delay caller) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (liftWGPrefix (armTimer pid timer delay caller))
      (fun r => Event.armed ⟨context,pid,timer,delay,caller,r⟩))
  exact recorded (liftWGPrefix (armTimer pid timer delay caller)) (armTimer pid timer delay caller) (erasesStatePrefix_lift _)
    (Driver.History.state_lift _) (fun _ _ _ => rfl) _
    (fun _ _ valid => ⟨valid,rfl⟩)

theorem queue (pid : PeerId) : Driver.StateHistorySafe Safe (effects.append pid) := by
  change Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? fun context =>
    receiptWGObserved (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
      (fun r => Event.queued ⟨context,pid,r⟩))
  exact recorded (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (erasesStatePrefix_lift _) (Driver.History.state_lift _) (fun _ _ _ => rfl) _
    (fun _ _ valid => ⟨valid,rfl⟩)

theorem effects_safe : Driver.EffectsHistory Safe effects where
  step := Driver.History.state_lift
  arm := arm
  append := queue

theorem derived (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact Driver.History.state_bind (Driver.effects_modify_history effects_safe _ _ _ _)
    (fun _ => Driver.History.state_pure _)

theorem initiated (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' effect_history_step effects_safe

theorem protocol_send (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  ProtocolSocket.observed_history Safe Event.protocolSocket scope?
    (fun _ _ _ hi valid => hi.emit ⟨valid,rfl⟩) pid bytes

theorem cookie_send (mac : HandshakeMac)
    (native : mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded))
    (loaded : mac.loaded = true) (state : mac.checked.value = .noCookie)
    (kind : messageType mac.input = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType mac.input = MESSAGE_HANDSHAKE_RESPONSE) :
    Driver.StateHistorySafe Safe (CookieSocket.observed Event.cookieSocket mac mac.input mac.source) :=
  CookieCaller.observed_history Safe Event.cookieSocket mac native loaded state kind
    (fun _ _ hi valid qualifying kind => hi.emit ⟨valid,qualifying,kind⟩)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
