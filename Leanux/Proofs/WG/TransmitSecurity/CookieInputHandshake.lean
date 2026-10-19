import Leanux.Proofs.WG.TransmitSecurity.CookieInputHistory

/-! Input-length history through the actual MAC decision and receive source.
The callback consumes the same input captured by that native decision. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CookieInput
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open AuthenticatedEffects.CausalJournal HandshakeSecurity Origins.HandshakeSources CookieCaller
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem effects_safe : Driver.EffectsHistory Safe effects where
  step := Driver.History.state_lift
  arm := by
    intro pid timer delay caller w a h hi
    exact receipt_quiet (liftWGPrefix (armTimer pid timer delay caller))
      (Driver.History.state_lift _)
      (fun r => Event.armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩)
      (fun _ => True.intro) w a h hi
  append := by
    intro pid w a h hi
    exact receipt_quiet (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
      (Driver.History.state_lift _)
      (fun r => Event.queued ⟨CausalScope.current scope? h,pid,r⟩)
      (fun _ => True.intro) w a h hi

theorem derived (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact Driver.History.state_bind (Driver.effects_modify_history effects_safe _ _ _ _)
    (fun _ => Driver.History.state_pure _)

theorem protocol_send (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  ProtocolSocket.observed_history Safe Event.protocolSocket scope?
    (fun _ _ _ hi _ => hi.emit True.intro) pid bytes

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) : Driver.StateHistorySafe Safe
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  Driver.History.state_bind (emit_quiet _ True.intro) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) :
    Driver.StateHistorySafe Safe
      (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? body) :=
  quiet_state (Event.old ∘ Journal.Event.handshake) handshake? (fun _ => True.intro) body

private theorem other
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid))
    (mac : HandshakeMac) :
    CookieCaller.OtherSafe Safe
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ Journal.Event.handshake) effects))) := by
  constructor
  · intro α action; rfl
  all_goals intros
  all_goals simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  all_goals repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CausalScope.scope; apply state_scope)
    | (driver_history_head receiptWGObserved; apply receipt_quiet)
    | (driver_history_head HandshakeWorker.callback; apply callback)
    | (driver_history_head HandshakeWorker.old; exact old _)
    | (driver_history_head TimerEffects.derivedWith; exact derived _)
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | exact hs _
    | exact hk _
    | trivial
    | driver_state_history_step


theorem receive_valid_history
    (msg : Key) (consume : Key → WGPrefix Event Unit)
    (consumeSafe : ∀ msg, Driver.StateHistorySafe Safe (consume msg))
    (make : HandshakeMac → Ops (WGPrefix Event))
    (other : ∀ mac, mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      OtherSafe Safe (make mac))
    (cookie : ∀ mac, mac.input = msg → mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      mac.loaded = true → mac.checked.value = .noCookie →
      (messageType mac.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType mac.input = MESSAGE_HANDSHAKE_RESPONSE) →
      Driver.StateHistorySafe Safe ((make mac).cookie mac.input mac.source))
    (src : SkbSource) :
    Driver.StateHistorySafe Safe (CookieConsumption.receiveWith consume make msg src) := by
  unfold CookieConsumption.receiveWith
  apply Driver.History.state_bind (Driver.History.state_lift _)
  intro isCookie
  split
  · exact Driver.History.state_bind (consumeSafe msg)
      (fun _ => Driver.History.state_pure _)
  · apply Driver.History.state_bind (Driver.History.state_lift _)
    intro loaded
    have captured : StatePrefixEnsures (fun h _ _ => Safe h) Safe
        (captureWGRun (cookieValidatePacket msg src loaded))
        (fun receipt h _ _ => Safe h ∧ receipt.Valid (cookieValidatePacket msg src loaded)) := by
      apply StatePrefixEnsures.captureWGRun (P := fun h _ _ => Safe h) (S := Safe) _
        (fun _ _ _ hi => hi)
      intro h w a value v b hi run
      exact ⟨hi,run⟩
    apply StatePrefixEnsures.bind captured
    intro checked w a h hi
    exact after_mac (other ⟨msg,src,loaded,checked⟩ hi.2) msg src loaded checked.value
      (cookie ⟨msg,src,loaded,checked⟩ rfl hi.2) w a h hi.1


theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) (msg : Key) (src : SkbSource)
    (valid : HeaderLength.Valid msg) :
    Driver.StateHistorySafe Safe (CookieConsumption.receiveWith (CookieConsumption.observed Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  apply receive_valid_history
  · intro packet
    exact CookieConsumption.observed_history Safe Event.cookieConsumed packet
      (fun h receipt hi _ => hi.emit True.intro)
  · intro mac _
    exact other session keepalive hs hk mac
  · intro mac input _ _ _ _
    apply cookie
    rw [input]
    exact valid

end Leanux.Proofs.WG.TransmitSecurity.CookieInput
