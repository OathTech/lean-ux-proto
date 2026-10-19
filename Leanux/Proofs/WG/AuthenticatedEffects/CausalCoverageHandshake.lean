import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames

/-! The actual authenticated handshake callbacks establish their own scopes
before any delayed effect or staging. Native refusal/consumer observations do
not gain a fabricated caller context. Authentication is supplied separately by
the initialized admission/callback pairing theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "coverage_handshake_callback " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateAt do throwError "not a state coverage contract"
  let arguments := target.getAppArgs
  unless arguments.size > 0 do throwError "missing callback"
  let action := arguments.back!.consumeMData.headBeta
  let callback ← getFVarId wanted
  unless action.getAppFn == .fvar callback do throwError "different callback"

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
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,
    StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact quiet_state (CallbackFrames.initiation_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact quiet_state (CallbackFrames.response_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact quiet_state (CallbackFrames.cookie_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head StagedDisposal.Decoration.release; exact state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) (fun _ h => h.elim) _)
    | (coverage_head ProtocolSocket.observed; exact protocol_send _ _ (by assumption))
    | (coverage_head CookieSocket.observed; exact cookie_send _ _ _)
    | (coverage_head CausalScope.scope; apply state_scope (.handshake _ _) True.intro; intro frames live)
    | (coverage_head receiptWGObserved; apply state_receipt)
    | (coverage_head HandshakeWorker.callback; apply callback)
    | (coverage_head HandshakeWorker.old; exact old _)
    | (coverage_head TimerEffects.derivedWith; exact derived _ (by assumption))
    | (coverage_head TimerEffects.traversalWith; exact traversal _ (by assumption))
    | (coverage_handshake_callback session; exact hs _ _ (by assumption))
    | (coverage_handshake_callback keepalive; exact hk _ _ (by assumption))
    | (intro r impossible; exact impossible.elim)
    | (first | rfl | exact True.intro)
    | coverage_state_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateGuarded (session pid)) (hk : ∀ pid, StateGuarded (keepalive pid))
    (msg : Key) (src : SkbSource) : StateAt frames (CookieConsumption.receiveWith (RetirementSecurity.NestedPeerRelease.cookieObserved CallbackFrames.nested Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ Journal.Event.handshake) effects))) msg src) := by
  unfold CookieConsumption.receiveWith
  repeat' first
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact quiet_state (CallbackFrames.initiation_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact quiet_state (CallbackFrames.response_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact quiet_state (CallbackFrames.cookie_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head StagedDisposal.Decoration.release; exact state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) (fun _ h => h.elim) _)
    | (coverage_head receiptWGObserved; refine state_receipt _ ?_ _ (fun _ => rfl) (fun _ impossible => impossible.elim))
    | (coverage_head ProtocolSocket.observed; exact protocol_send _ _ (by assumption))
    | (coverage_head CookieSocket.observed; exact cookie_send _ _ _)
    | (coverage_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (coverage_head captureWGRun; exact state_capture _ (state_lift _))
    | coverage_state_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateGuarded (session pid)) (hk : ∀ pid, StateGuarded (keepalive pid)) :
    StateAt frames (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact quiet_state (CallbackFrames.initiation_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact quiet_state (CallbackFrames.response_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact quiet_state (CallbackFrames.cookie_quiet observed? (fun _ => rfl) (fun _ => rfl) _))
    | (coverage_head StagedDisposal.Decoration.release; exact state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) (fun _ h => h.elim) _)
    | (coverage_head ProtocolSocket.observed; exact protocol_send _ _ (by assumption))
    | (coverage_head CookieSocket.observed; exact cookie_send _ _ _)
    | (coverage_head CookieConsumption.receiveWith; exact receive session keepalive hs hk _ _)
    | coverage_state_step

theorem handshake_worker : StateAt frames (Driver.handshakeObserved hooks) :=
  handshake hooks.session (Driver.keepaliveObserved hooks) (fun pid _ live => session pid live)
    (fun pid _ live => keepalive pid live)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
