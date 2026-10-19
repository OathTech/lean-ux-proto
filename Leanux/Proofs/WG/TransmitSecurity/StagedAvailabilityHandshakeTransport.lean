import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHandshakeAdapters

/-! The complete native handshake driver transports available staged births through its
actual session and keepalive callbacks, preserving stopped history prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
open Leanux.Proofs.WG.Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "available_origin_function " wanted:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a staged-availability state contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let expected ← Lean.Elab.Term.elabTerm wanted none
  unless action.consumeMData.headBeta.getAppFn == expected do throwError "different supplied callback"

theorem cookie_consumed_observed (msg : Key) :
    StateSafe (CookieConsumption.observed Event.cookieConsumed msg) :=
  state_receipt (state_lift _ (fun _ => Native.cookie_consume msg)) _ (fun _ => rfl)

macro "available_handshake_observation" : tactic => `(tactic| first
  | (available_origin_head CookieConsumption.observed; exact cookie_consumed_observed _)
  | (available_origin_head ProtocolSocket.observed; exact protocol_send_observed _ _)
  | (available_origin_head CookieSocket.observed; exact cookie_send_observed _ _ _)
  | (available_origin_head liftWGPrefix; apply state_lift; intro history; repeat' staged_available_native; done)
  | staged_available_native)

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
    | (available_origin_head CausalScope.scope; apply state_scope)
    | (available_origin_head receiptWGObserved; apply state_receipt; try (intro r; rfl))
    | (available_origin_head HandshakeWorker.callback; apply handshake_callback)
    | (available_origin_old_head HandshakeCausal.initiation; exact handshake_initiation _)
    | (available_origin_old_head HandshakeCausal.response; exact handshake_response _)
    | (available_origin_old_head HandshakeCausal.call; apply handshake_call; intro history)
    | (available_origin_head TimerEffects.derivedWith; exact derived_observed _)
    | (available_origin_head TimerEffects.traversalWith; exact traversal_observed _)
    | (available_origin_function session; exact hs _)
    | (available_origin_function keepalive; exact hk _)
    | available_handshake_observation
    | trivial
    | available_origin_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (msg : Key) (src : SkbSource) : StateSafe (CookieConsumption.receiveWith (CookieConsumption.observed Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (ProtocolSender.receiveOps (Event.old ∘ TransmitSecurity.Journal.Event.handshake)
              handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket)
            (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects))) msg src) := by
  unfold CookieConsumption.receiveWith
  repeat' first
    | (available_origin_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (available_origin_head captureWGRun; change StateSafe (captureWGObserved (liftWGPrefix _)); apply state_capture)
    | available_handshake_observation
    | trivial
    | available_origin_step

theorem handshake_carrier
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid)) :
    StateSafe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (available_origin_head CookieConsumption.receiveWith; exact receive session keepalive hs hk _ _)
    | available_handshake_observation
    | trivial
    | available_origin_step


theorem handshake_observed : StateSafe (Driver.handshakeObserved hooks) :=
  handshake_carrier CausalJournal.session (Driver.keepaliveObserved hooks)
    session_observed keepalive_observed_source

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
