import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalHandshakePairFrames

/-! The actual native handshake worker emits each lexical entry immediately
before its corresponding callback, including completed-exchange decorations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem nested_safe : RetirementSecurity.NestedPeerRelease.Ops.History Safe
    (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?) where
  step := Driver.History.state_lift
  release := fun _ => quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _

private theorem nested_initiation (mac : HandshakeMac) : Driver.StateHistorySafe Safe
    (RetirementSecurity.NestedPeerRelease.admitInitiationWith
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?)
      (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission) mac) :=
  CallbackHistory.initiation nested_safe
    (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission)
    (fun event => emit_quiet (.old (.handshake (.admission event))) rfl) mac

private theorem nested_response (mac : HandshakeMac) : Driver.StateHistorySafe Safe
    (RetirementSecurity.NestedPeerRelease.admitResponseWith
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?)
      (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission) mac) :=
  CallbackHistory.response nested_safe
    (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission)
    (fun event => emit_quiet (.old (.handshake (.admission event))) rfl) mac

private theorem nested_cookie (msg : Key) : Driver.StateHistorySafe Safe
    (RetirementSecurity.NestedPeerRelease.cookieObserved
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?)
      Event.cookieConsumed msg) :=
  CallbackHistory.cookie nested_safe
    (RetirementSecurity.NestedPeerRelease.observedOps_erases _ _) Event.cookieConsumed
    (fun _ receipt hi _ => hi.emit (.cookieConsumed receipt) rfl) msg

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) : Driver.StateHistorySafe Safe
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  Driver.History.state_bind (emit_quiet _ rfl) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) :
    Driver.StateHistorySafe Safe
      (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? body) :=
  quiet_state (Event.old ∘ Journal.Event.handshake) handshake? (fun _ => rfl) body

private theorem after_mac
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Driver.StateHistorySafe Safe (afterMacWith
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps,HandshakeEffects.old_call,receipt_callback]
  repeat' first
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact nested_initiation _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact nested_response _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact nested_cookie _)
    | (driver_history_head StagedDisposal.Decoration.release; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head CausalScope.scope; apply scoped_callback)
    | (driver_history_head receiptWGObserved; apply receipt_quiet)
    | (driver_history_head HandshakeWorker.callback; apply callback)
    | (driver_history_head HandshakeWorker.old; exact old _)
    | (driver_history_head TimerEffects.derivedWith; exact derived _)
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | exact hs _
    | exact hk _
    | trivial
    | driver_state_history_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) (msg : Key) (src : SkbSource) :
    Driver.StateHistorySafe Safe (CookieConsumption.receiveWith (RetirementSecurity.NestedPeerRelease.cookieObserved
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?) Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  unfold CookieConsumption.receiveWith
  repeat' first
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact nested_initiation _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact nested_response _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact nested_cookie _)
    | (driver_history_head receiptWGObserved; refine receipt_quiet _ ?_ _ (fun _ => rfl))
    | (driver_history_head StagedDisposal.Decoration.release; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (driver_history_head captureWGRun; exact (Driver.History.state_lift _).captureWGObserved)
    | driver_state_history_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) :
    Driver.StateHistorySafe Safe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact nested_initiation _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact nested_response _)
    | (driver_history_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact nested_cookie _)
    | (driver_history_head StagedDisposal.Decoration.release; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head CookieConsumption.receiveWith; exact receive session keepalive hs hk _ _)
    | driver_state_history_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
