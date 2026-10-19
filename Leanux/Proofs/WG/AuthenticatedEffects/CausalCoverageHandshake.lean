import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! The actual authenticated handshake callbacks establish their own scopes
before any delayed effect or staging. Native refusal/consumer observations do
not gain a fabricated caller context. Authentication is supplied separately by
the initialized admission/callback pairing theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : StateAt frames body) : StateAt frames
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  state_bind (state_emit _ rfl (fun impossible => impossible.elim)) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) : StateAt frames
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? body) :=
  state_focus (Event.old ∘ Journal.Event.handshake) handshake?
    (fun _ => rfl) (fun _ impossible => impossible.elim) body

private theorem after_mac
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateGuarded (session pid)) (hk : ∀ pid, StateGuarded (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateAt frames (afterMacWith
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (HandshakeWorker.observedOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    HandshakeWorker.observedOps]
  repeat' first
    | (coverage_head CausalScope.scope; apply state_scope; intro frames live)
    | (coverage_head receiptWGObserved; apply state_receipt)
    | (coverage_head HandshakeWorker.callback; apply callback)
    | (coverage_head HandshakeWorker.old; exact old _)
    | (coverage_head TimerEffects.derivedWith; exact derived _ (by assumption))
    | (coverage_head TimerEffects.traversalWith; exact traversal _ (by assumption))
    | exact hs _ _ (by assumption)
    | exact hk _ _ (by assumption)
    | (intro r impossible; exact impossible.elim)
    | trivial
    | coverage_state_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateGuarded (session pid)) (hk : ∀ pid, StateGuarded (keepalive pid))
    (msg : Key) (src : SkbSource) : StateAt frames (HandshakeWorker.receiveWith
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (HandshakeWorker.observedOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  unfold HandshakeWorker.receiveWith
  repeat' first
    | (coverage_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (coverage_head captureWGRun; exact state_capture _ (state_lift _))
    | coverage_state_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateGuarded (session pid)) (hk : ∀ pid, StateGuarded (keepalive pid)) :
    StateAt frames (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake HandshakeWorker.observedWith HandshakeWorker.workerWith
  repeat' first
    | (coverage_head HandshakeWorker.receiveWith; exact receive session keepalive hs hk _ _)
    | coverage_state_step

theorem handshake_worker : StateAt frames (Driver.handshakeObserved hooks) :=
  handshake hooks.session (Driver.keepaliveObserved hooks) (fun pid _ live => session pid live)
    (fun pid _ live => keepalive pid live)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
