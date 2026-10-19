import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeStaging

/-! Native authenticated callbacks balance their own scopes, allowing nested
keepalive and session observers while retaining valid prefixes on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : StateSafe body) : StateSafe
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  state_bind (state_emit _ rfl) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) :
    StateSafe
      (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? body) :=
  state_focus (Event.old ∘ Journal.Event.handshake) handshake? (fun _ => rfl) body

private theorem after_mac
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid))
    (hk : ∀ pid, StateSafe (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (scope_balance_head ProtocolSocket.observed; exact protocol_send _ _)
    | (scope_balance_head CookieSocket.observed; exact cookie_send _ _ _)
    | (scope_balance_head CausalScope.scope; apply state_scope)
    | (scope_balance_head receiptWGObserved; apply state_receipt)
    | (scope_balance_head HandshakeWorker.callback; apply callback)
    | (scope_balance_head HandshakeWorker.old; exact old _)
    | (scope_balance_head TimerEffects.derivedWith; exact derived _)
    | (scope_balance_head TimerEffects.traversalWith; exact traversal _)
    | exact hs _
    | exact hk _
    | trivial
    | scope_state_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid))
    (hk : ∀ pid, StateSafe (keepalive pid)) (msg : Key) (src : SkbSource) :
    StateSafe (HandshakeWorker.receiveWith
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  unfold HandshakeWorker.receiveWith
  repeat' first
    | (scope_balance_head ProtocolSocket.observed; exact protocol_send _ _)
    | (scope_balance_head CookieSocket.observed; exact cookie_send _ _ _)
    | (scope_balance_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (scope_balance_head captureWGRun; exact state_capture _ (state_lift _))
    | scope_state_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid))
    (hk : ∀ pid, StateSafe (keepalive pid)) :
    StateSafe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake HandshakeWorker.observedWith HandshakeWorker.workerWith
  repeat' first
    | (scope_balance_head ProtocolSocket.observed; exact protocol_send _ _)
    | (scope_balance_head CookieSocket.observed; exact cookie_send _ _ _)
    | (scope_balance_head HandshakeWorker.receiveWith; exact receive session keepalive hs hk _ _)
    | scope_state_step


theorem handshake_worker : StateSafe (Driver.handshakeObserved hooks) :=
  handshake hooks.session (Driver.keepaliveObserved hooks) session keepalive

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
