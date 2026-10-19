import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuiet

/-! The actual callback retains earlier delivery certificates; its emitted
metadata does not add a delivery boundary. Native emission accounting remains
a separate source contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

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
            (StagedDisposal.Decoration.receive Event.stagedDisposal stagedDisposal?
              (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket))
            (Event.old ∘ Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head CausalScope.scope; apply state_scope; try (intro; rfl))
    | (driver_history_head receiptWGObserved; apply receipt_quiet)
    | (driver_history_head HandshakeWorker.callback; apply callback)
    | (driver_history_head HandshakeWorker.old; exact old _)
    | (driver_history_head TimerEffects.derivedWith; exact derived _)
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | exact hs _
    | exact hk _
    | trivial
    | (driver_history_head StagedDisposal.Decoration.release; exact peer_release _)
    | driver_state_history_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) (msg : Key) (src : SkbSource) :
    Driver.StateHistorySafe Safe (CookieConsumption.receiveWith (CookieConsumption.observed Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (StagedDisposal.Decoration.receive Event.stagedDisposal stagedDisposal?
              (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac Event.protocolSocket scope? Event.cookieSocket))
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  unfold CookieConsumption.receiveWith CookieConsumption.observed
  repeat' first
    | (driver_history_head receiptWGObserved; refine receipt_quiet _ ?_ _ (fun _ => rfl))
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (driver_history_head captureWGRun; exact (Driver.History.state_lift _).captureWGObserved)
    | (driver_history_head StagedDisposal.Decoration.release; exact peer_release _)
    | driver_state_history_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Safe (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Safe (keepalive pid)) :
    Driver.StateHistorySafe Safe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head CookieConsumption.receiveWith; exact receive session keepalive hs hk _ _)
    | (driver_history_head StagedDisposal.Decoration.release; exact peer_release _)
    | driver_state_history_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
