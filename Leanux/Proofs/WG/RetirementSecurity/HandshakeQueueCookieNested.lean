import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCookieActors

/-! Header-length authorization through the actual nested consumer source.
Repayment receipts preserve the input's cookie-socket obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects
open CausalJournal CookieInput HandshakeSecurity Origins.HandshakeSources CookieCaller
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

abbrev receiver (session : PeerId→WGPrefix Event Bool) (keepalive : PeerId→WGPrefix Event Unit) :=
  CookieConsumption.receiveWith (NestedPeerRelease.cookieObserved CallbackFrames.nested Event.cookieConsumed)
    (fun mac=>HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
      (ExchangeJoint.receiveOps Event.exchange
        (HandshakeEffects.withEffects (CausalJournal.receiveOps session keepalive mac)
          (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects)))

private theorem nested_callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) : Driver.StateHistorySafe Safe
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  Driver.History.state_bind (emit_quiet _ True.intro) (fun _ => preserves)

private theorem nested_old (body : WGPrefix HandshakeCausal.Event α) :
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
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) := by
  constructor
  · intro α action; rfl
  all_goals intros
  all_goals simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  all_goals repeat' first
    | (driver_history_head NestedPeerRelease.admitInitiationWith;
       exact callback_state (CallbackFrames.initiation_quiet cookieOnly (fun _=>rfl) (fun _=>rfl) _))
    | (driver_history_head NestedPeerRelease.admitResponseWith;
       exact callback_state (CallbackFrames.response_quiet cookieOnly (fun _=>rfl) (fun _=>rfl) _))
    | (driver_history_head StagedDisposal.Decoration.release;
       exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => True.intro) _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CausalScope.scope; apply state_scope)
    | (driver_history_head receiptWGObserved; apply receipt_quiet)
    | (driver_history_head HandshakeWorker.callback; apply nested_callback)
    | (driver_history_head HandshakeWorker.old; exact nested_old _)
    | (driver_history_head TimerEffects.derivedWith; exact derived _)
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | exact hs _
    | exact hk _
    | trivial
    | driver_state_history_step


theorem receive_nested
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) (msg : Key) (src : SkbSource)
    (valid : HeaderLength.Valid msg) :
    Driver.StateHistorySafe Safe (receiver session keepalive msg src) := by
  apply CookieInput.receive_valid_history
  · intro packet
    exact callback_state (CallbackFrames.cookie_quiet cookieOnly (fun _=>rfl) (fun _=>rfl) packet)
  · intro mac _
    exact other session keepalive hs hk mac
  · intro mac input _ _ _ _
    apply cookie
    rw [input]
    exact valid

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
