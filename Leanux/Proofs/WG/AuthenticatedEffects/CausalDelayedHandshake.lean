import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedNative

/-! The final journal's actual handshake receiver transports live delayed
occurrences through its native cookie/consumer callbacks, lexical scopes and
effect callbacks. Session and keepalive preserve contracts remain explicit
until the corresponding shared driver actors discharge them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open HandshakeSecurity Origins.HandshakeSources TimerSlots
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : StateSafe body) : StateSafe
    (HandshakeWorker.callback (Event.old ∘ TransmitSecurity.Journal.Event.handshake) kind pid body) :=
  state_bind (state_emit _) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (safe : StateSafe (liftWGPrefix native)) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake? body) :=
  observed_native _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _) safe

private theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (safe : StateSafe (liftWGPrefix native)) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.call kind pid native)) := old _ _ (HandshakeCausal.call_erases kind pid native) safe

private theorem old_initiation (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.initiation mac)) :=
  old _ _ (HandshakeCausal.initiation_erases mac)
    (state_framed _ (consumeInitiation_retained mac.input) (SendWorkCauses.initiation_frame mac.input))

private theorem old_response (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.response mac)) :=
  old _ _ (HandshakeCausal.response_erases mac)
    (state_framed _ (consumeResponse_retained mac.input) (SendWorkCauses.response_frame mac.input))

theorem protocol_send (pid : PeerId) (bytes : List UInt8) :
    StateSafe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  observed_native _ _ (ProtocolSocket.observed_erases _ _ _ _) (ProtocolSocket.observed_appends _ _ _ _)
    (state_framed _ (sendBufferToPeer_retained pid bytes) (SendWorkCauses.send_frame pid bytes))

theorem cookie_send (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    StateSafe (CookieSocket.observed Event.cookieSocket mac msg src) :=
  observed_native _ _ (CookieSocket.observed_erases _ _ _ _) (CookieSocket.observed_appends _ _ _ _)
    (state_framed _ (cookieSend_retained msg src) (SendWorkCauses.cookie_send_frame msg src))

open Lean Meta Elab Tactic in
elab "causal_delayed_old_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a delayed state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``HandshakeWorker.old do throwError "not an old handshake callback"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := body.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

open Lean Meta Elab Tactic in
elab "causal_delayed_function " wanted:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a delayed state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← Lean.Elab.Term.elabTerm wanted none
  unless action.getAppFn == expected do throwError "different supplied callback"

macro "causal_delayed_handshake_native" : tactic => `(tactic| first
  | (causal_delayed_head ProtocolSocket.observed; exact protocol_send _ _)
  | (causal_delayed_head CookieSocket.observed; exact cookie_send _ _ _)
  | (causal_delayed_native_head createResponse; exact state_framed _ (createResponse_retained _) (SendWorkCauses.response_create_frame _))
  | (causal_delayed_native_head addMacToPacket; exact state_framed _ (addMac_retained _ _) (SendWorkCauses.mac_frame _ _))
  | (causal_delayed_native_head sendBufferToPeer; exact state_framed _ (sendBufferToPeer_retained _ _) (SendWorkCauses.send_frame _ _))
  | (causal_delayed_native_head setPeerEndpointFromSkb; exact state_framed _ (endpoint_retained _ _) (SendWorkCauses.endpoint_frame _ _))
  | (causal_delayed_native_head timersHandshakeComplete; exact handshake_complete _ _)
  | (causal_delayed_native_head timersAnyAuthenticatedPacketSent; exact delete _ _)
  | (causal_delayed_native_head timersAnyAuthenticatedPacketReceived; exact delete _ _)
  | (causal_delayed_native_head sendHandshakeCookie; exact state_framed _ (cookieSend_retained _ _) (SendWorkCauses.cookie_send_frame _ _))
  | (causal_delayed_native_head cookieMessageConsume; exact state_framed _ (cookieConsume_retained _) (SendWorkCauses.cookie_consume_frame _))
  | (causal_delayed_native_head Cookies.loadPhase; exact state_framed _ (retained_store Cookies.loadPhase_sameStore) SendWorkCauses.load_frame)
  | (causal_delayed_native_head cookieValidatePacket; exact state_framed _ (cookie_retained (cookieValidatePacket_sameCookie _ _ _)) (SendWorkCauses.validate_frame _ _ _))
  | (causal_delayed_head liftWGPrefix; solve | causal_delayed_native))

private theorem after_mac
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ TransmitSecurity.Journal.Event.handshake)
              handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (causal_delayed_head CausalScope.scope; apply state_scope)
    | (causal_delayed_head receiptWGObserved; apply state_receipt)
    | (causal_delayed_head HandshakeWorker.callback; apply callback)
    | (causal_delayed_old_head HandshakeCausal.initiation; exact old_initiation _)
    | (causal_delayed_old_head HandshakeCausal.response; exact old_response _)
    | (causal_delayed_old_head HandshakeCausal.call; apply old_call)
    | (causal_delayed_head TimerEffects.derivedWith; exact derived _)
    | (causal_delayed_head TimerEffects.traversalWith; exact traversal _)
    | (causal_delayed_function session; exact hs _)
    | (causal_delayed_function keepalive; exact hk _)
    | causal_delayed_handshake_native
    | causal_delayed_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (msg : Key) (src : SkbSource) : StateSafe (HandshakeWorker.receiveWith
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ TransmitSecurity.Journal.Event.handshake)
              handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects))) msg src) := by
  unfold HandshakeWorker.receiveWith
  repeat' first
    | (causal_delayed_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (causal_delayed_head captureWGRun; apply capture_native)
    | causal_delayed_handshake_native
    | causal_delayed_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid)) :
    StateSafe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake HandshakeWorker.observedWith HandshakeWorker.workerWith
  repeat' first
    | (causal_delayed_head HandshakeWorker.receiveWith; exact receive session keepalive hs hk _ _)
    | causal_delayed_handshake_native
    | causal_delayed_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
