import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCallbackFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionEffects
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCookie
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionHandshakeFrames

/-! Ordered emission accounting through the actual handshake receive worker.
The protocol and cookie leaves account for their own native appends; every
other callback is independently framed as send-free. Session and keepalive
contracts remain explicit until the corresponding driver actors close them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open HandshakeSecurity Origins.HandshakeSources TimerSlots
set_option maxHeartbeats 800000
set_option maxRecDepth 4096


private theorem nested_initiation (mac : HandshakeMac) : StateSafe
    (RetirementSecurity.NestedPeerRelease.admitInitiationWith CallbackFrames.nested CallbackFrames.admissionRecord mac) :=
  state_callback _ (CallbackFrames.initiation_quiet contributing? (fun _ => rfl) (fun _ => rfl) mac)
    (CallbackFrames.initiation_erases mac) (consumeInitiation_sent mac.input)

private theorem nested_response (mac : HandshakeMac) : StateSafe
    (RetirementSecurity.NestedPeerRelease.admitResponseWith CallbackFrames.nested CallbackFrames.admissionRecord mac) :=
  state_callback _ (CallbackFrames.response_quiet contributing? (fun _ => rfl) (fun _ => rfl) mac)
    (CallbackFrames.response_erases mac) (consumeResponse_sent mac.input)

private theorem nested_cookie (msg : Key) : StateSafe
    (RetirementSecurity.NestedPeerRelease.cookieObserved CallbackFrames.nested Event.cookieConsumed msg) :=
  state_callback _ (CallbackFrames.cookie_quiet contributing? (fun _ => rfl) (fun _ => rfl) msg)
    (CallbackFrames.cookie_erases msg) (cookieMessageConsume_sent msg)

private theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (preserves : StateSafe body) : StateSafe
    (HandshakeWorker.callback (Event.old ∘ TransmitSecurity.Journal.Event.handshake) kind pid body) :=
  state_bind (state_emit _ rfl) (fun _ => preserves)

private theorem old (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake? body) :=
  state_observed _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (focus_state_quiet _ _ (fun _ => rfl) _) frame

private theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (frame : SameView WGWorld.sent native) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.call kind pid native)) := old _ _ (HandshakeCausal.call_erases kind pid native) frame

private theorem old_initiation (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.initiation mac)) :=
  old _ _ (HandshakeCausal.initiation_erases mac)
    (consumeInitiation_sent mac.input)

private theorem old_response (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
      (HandshakeCausal.response mac)) :=
  old _ _ (HandshakeCausal.response_erases mac)
    (consumeResponse_sent mac.input)

open Lean Meta Elab Tactic in
elab "emission_old_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not an emission state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``HandshakeWorker.old do throwError "not an old handshake callback"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := body.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

open Lean Meta Elab Tactic in
elab "emission_function " wanted:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not an emission state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← Lean.Elab.Term.elabTerm wanted none
  unless action.getAppFn == expected do throwError "different supplied callback"

open Lean Meta Elab Tactic in
elab "emission_frame_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``SameView do throwError "not a native view frame"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant native source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native source"

macro "emission_handshake_frame" : tactic => `(tactic| first
  | (emission_frame_head createResponse; exact EmissionFrames.create_response _)
  | (emission_frame_head addMacToPacket; exact EmissionFrames.mac _ _)
  | (emission_frame_head setPeerEndpointFromSkb; exact EmissionFrames.endpoint _ _)
  | (emission_frame_head timersHandshakeComplete; exact EmissionFrames.completed _ _)
  | (emission_frame_head timersAnyAuthenticatedPacketSent; exact EmissionFrames.delete _ _)
  | (emission_frame_head timersAnyAuthenticatedPacketReceived; exact EmissionFrames.delete _ _)
  | (emission_frame_head Bind.bind; sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec]))

macro "emission_handshake_native" : tactic => `(tactic| first
  | (emission_head RetirementSecurity.NestedPeerRelease.admitInitiationWith; exact nested_initiation _)
  | (emission_head RetirementSecurity.NestedPeerRelease.admitResponseWith; exact nested_response _)
  | (emission_head RetirementSecurity.NestedPeerRelease.cookieObserved; exact nested_cookie _)
  | (emission_head ProtocolSocket.observed; exact protocol_buffer _ _)
  | (emission_head CookieSocket.observed; exact cookie _ _ _)
  | (emission_native_head createResponse; exact state_native _ (EmissionFrames.create_response _))
  | (emission_native_head addMacToPacket; exact state_native _ (EmissionFrames.mac _ _))
  | (emission_native_head setPeerEndpointFromSkb; exact state_native _ (EmissionFrames.endpoint _ _))
  | (emission_native_head timersHandshakeComplete; exact state_native _ (EmissionFrames.completed _ _))
  | (emission_native_head timersAnyAuthenticatedPacketSent; exact state_native _ (EmissionFrames.delete _ _))
  | (emission_native_head timersAnyAuthenticatedPacketReceived; exact state_native _ (EmissionFrames.delete _ _))
  | (emission_native_head cookieMessageConsume; exact state_native _ (cookieMessageConsume_sent _))
  | (emission_native_head Cookies.loadPhase; exact state_native _ loadPhase_sent)
  | (emission_native_head cookieValidatePacket; exact state_native _ (cookieValidatePacket_sent _ _ _))
  | emission_effect_native)

private theorem after_mac
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith
      (HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects))) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (emission_head CausalScope.scope; apply state_scope)
    | (emission_head receiptWGObserved; refine state_receipt _ ?_ _ (fun _ => rfl))
    | (emission_head HandshakeWorker.callback; apply callback)
    | (emission_old_head HandshakeCausal.initiation; exact old_initiation _)
    | (emission_old_head HandshakeCausal.response; exact old_response _)
    | (emission_old_head HandshakeCausal.call; apply old_call; emission_handshake_frame)
    | (emission_head TimerEffects.derivedWith; exact derived _)
    | (emission_head TimerEffects.traversalWith; exact traversal _)
    | (emission_function session; exact hs _)
    | (emission_function keepalive; exact hk _)
    | (emission_head StagedDisposal.Decoration.release; exact peer_release _)
    | emission_handshake_native
    | emission_step

private theorem receive
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (msg : Key) (src : SkbSource) : StateSafe (CookieConsumption.receiveWith (RetirementSecurity.NestedPeerRelease.cookieObserved CallbackFrames.nested Event.cookieConsumed)
      (fun mac => HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
        (ExchangeJoint.receiveOps Event.exchange
          (HandshakeEffects.withEffects
            (CausalJournal.receiveOps session keepalive mac)
            (Event.old ∘ TransmitSecurity.Journal.Event.handshake) effects))) msg src) := by
  unfold CookieConsumption.receiveWith
  repeat' first
    | (emission_head receiptWGObserved; refine state_receipt _ ?_ _ (fun _ => rfl))
    | (emission_head afterMacWith; exact after_mac session keepalive hs hk _ _ _ _ _)
    | (emission_head captureWGRun; exact (state_native _ (cookieValidatePacket_sent _ _ _)).captureWGObserved)
    | (emission_head StagedDisposal.Decoration.release; exact peer_release _)
    | emission_handshake_native
    | emission_step

theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid)) :
    StateSafe (CausalJournal.handshake session keepalive) := by
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (emission_head CookieConsumption.receiveWith; exact receive session keepalive hs hk _ _)
    | (emission_head StagedDisposal.Decoration.release; exact peer_release _)
    | emission_handshake_native
    | emission_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
