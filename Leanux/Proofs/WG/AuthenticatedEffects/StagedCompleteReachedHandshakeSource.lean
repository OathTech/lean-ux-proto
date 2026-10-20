import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieRouteFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieNativeCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumerNativeCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPubkeyLookupSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieMetadataCanonical
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSessionCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolPointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutedTransmitComposition

/-! Fixed handshake worker source. Callback scopes, receipts, keepalive and
repayment are explicit. Consumer/session/socket atoms retain their existing
boundary contracts; their finer native interiors are separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal
open RetirementSecurity HandshakeSecurity Origins.HandshakeSources
abbrev History := List Event

inductive Native : Type 1 where
  | quiet {α : Type} (body : WG.M α) (frame : SameView StagedEntry.view body)
  | lookup {α : Type} (body : WG.M α) (source : Lookup.Shape body)
  | metadata {α : Type} (body : WG.M α) (source : PeerMetadata.Shape body)
  | capturedMetadata {α : Type} (body : WG.M α) (source : PeerMetadata.Shape body)
  | captured {α : Type} (body : WG.M α) (frame : SameView StagedEntry.view body)
  | session (pid : PeerId)
  | initiation (mac : HandshakeMac)
  | response (mac : HandshakeMac)
  | cookieConsumed (bytes : Key)
  | protocol (pid : PeerId) (bytes : Key)
  | cookie (mac : HandshakeMac) (bytes : Key) (src : SkbSource)
  | scope (event : CausalScope.Event Cause)
  | note (kind : HandshakeCausal.Kind) (pid : PeerId)
  | admission (event : HandshakeAdmission)
  | cookieReceipt (event : CookieConsumption.Receipt)
  | exchange (event : Exchange.Event)
  | cookieRoute (args : ProtocolSocket.Args)
  | cookieDatagram (receipt : CookieSocket.Receipt)
  | oldSession (pid : PeerId) (run : WGRunWitness Bool)

def Native.Result : Native → Type
  | @quiet α .. => α
  | @lookup α .. => α
  | @metadata α .. => α
  | @capturedMetadata α .. => WGRunWitness α
  | @captured α .. => WGRunWitness α
  | .cookieRoute _ => Except Int Route
  | .session _ => Bool
  | .initiation _ | .response _ => Option PeerId
  | _ => Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .quiet body _ => liftWGObserver (liftWGPrefix body)
  | .lookup body _ => liftWGObserver (liftWGPrefix body)
  | .metadata body _ => liftWGObserver (liftWGPrefix body)
  | .capturedMetadata body _ => liftWGObserver (captureWGRun body)
  | .captured body _ => liftWGObserver (captureWGRun body)
  | .session pid => liftWGObserver (CausalJournal.session pid)
  | .initiation mac => liftWGObserver (NestedPeerRelease.admitInitiationWith
      CompleteConsumers.nested ConsumerObserved.admission mac)
  | .response mac => liftWGObserver (NestedPeerRelease.admitResponseWith
      CompleteConsumers.nested ConsumerObserved.admission mac)
  | .cookieConsumed bytes => liftWGObserver (NestedPeerRelease.cookieObserved
      CompleteConsumers.nested Event.cookieConsumed bytes)
  | .protocol pid bytes => liftWGObserver (ProtocolSocket.observed Event.protocolSocket scope? pid bytes)
  | .cookie mac bytes src => liftWGObserver (CookieSocket.observed Event.cookieSocket mac bytes src)
  | .scope event => emitPrefix (.scope event)
  | .note kind pid => emitPrefix (.old (.handshake (.callback kind pid)))
  | .admission event => emitPrefix (ConsumerObserved.admission event)
  | .cookieReceipt event => emitPrefix (.cookieConsumed event)
  | .exchange event => emitPrefix (.exchange event)
  | .cookieRoute args => liftWGObserver (liftWGPrefix (CookieRoute.action args))
  | .cookieDatagram receipt => emitPrefix (.cookieSocket receipt)
  | .oldSession pid run => emitPrefix (.old (.responder (.session pid run)))

inductive Child where
  | keepalive (pid : PeerId)
  | release (peer : Option PeerId)

def Child.action : Child → PrefixM Event Unit
  | .keepalive pid => liftWGObserver (Driver.keepaliveObserved hooks pid)
  | .release peer => liftWGObserver (hooks.peerRelease peer)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | leaf (source : Consume.Leaf.Shape action) : Shape action
  | child (token : Child) : Shape token.action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def stateBindShape (body : WGPrefix Event α) (next : α → WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : WGPrefix Event α} (left : test → Shape (liftWGObserver yes))
    (right : ¬test → Shape (liftWGObserver no)) : Shape (liftWGObserver (if test then yes else no)) := by
  split
  · exact left ‹_›
  · exact right ‹_›

theorem scope_source (cause : Cause) (body : WGPrefix Event α) :
    liftWGObserver (CausalScope.scope Event.scope cause body) = (do
      let h←Consume.Leaf.historyRead
      emitPrefix (.scope (.entered ⟨h.length,cause⟩))
      let value←liftWGObserver body
      emitPrefix (.scope (.exited h.length))
      pure value) := by
  funext w h
  change runPrefix (liftWGObserver (CausalScope.scope Event.scope cause body)) w h =
    runPrefix (do
      let value←liftWGObserver body
      emitPrefix (.scope (.exited h.length))
      pure value) w (h++[.scope (.entered ⟨h.length,cause⟩)])
  rw [liftWGObserver_run,CausalScope.scope,CausalScope.withToken_run,runPrefix_bind,liftWGObserver_run]
  cases performed : runWGPrefix body w.wg w.ambient (h++[.scope (.entered ⟨h.length,cause⟩)]) with
  | mk result last=>cases result with
    | error reason=>rfl
    | ok pair=>rcases pair with ⟨⟨value,v⟩,a⟩;rfl

noncomputable def scopeShape (cause : Cause) (body : WGPrefix Event α)
    (source : Shape (liftWGObserver body)) : Shape (liftWGObserver (CausalScope.scope Event.scope cause body)) := by
  rw [scope_source]
  exact .bind (.leaf (.native .history)) fun h=>
    .bind (.native (.scope (.entered ⟨h.length,cause⟩))) fun _=>
      .bind source fun value=>.bind (.native (.scope (.exited h.length))) (fun _=>.pure value)

theorem receipt_source (body : WGPrefix Event α) (record : WGRunWitness α → Event) :
    liftWGObserver (receiptWGObserved body record) = (do
      let before←liftPrefix (get : Leanux.M World)
      let value←liftWGObserver body
      let after←liftPrefix (get : Leanux.M World)
      emitPrefix (record ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩)
      pure value) := by
  funext w h
  change runPrefix (liftWGObserver (receiptWGObserved body record)) w h = runPrefix (do
      let value←liftWGObserver body
      let after←liftPrefix (get : Leanux.M World)
      emitPrefix (record ⟨value,w.wg,after.wg,w.ambient,after.ambient⟩)
      pure value) w h
  rw [liftWGObserver_run,runWGPrefix_receiptWGObserved,runPrefix_bind,liftWGObserver_run]
  cases performed : runWGPrefix body w.wg w.ambient h with
  | mk result last=>cases result with
    | error reason=>rfl
    | ok pair=>rcases pair with ⟨⟨value,v⟩,a⟩;rfl

noncomputable def receiptShape (body : WGPrefix Event α) (record : WGRunWitness α → Event)
    (source : Shape (liftWGObserver body)) (events : ∀r,Shape (emitPrefix (record r))) :
    Shape (liftWGObserver (receiptWGObserved body record)) := by
  rw [receipt_source]
  exact .bind (.leaf (.native (.base (.basic .world)))) fun before=>
    .bind source fun value=>.bind (.leaf (.native (.base (.basic .world)))) fun after=>
      .bind (events ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩) (fun _=>.pure value)

noncomputable def callbackShape (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (source : Shape (liftWGObserver body)) : Shape (liftWGObserver
      (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body)) := by
  unfold HandshakeWorker.callback
  rw [liftWGObserver_bind]
  exact .bind (.native (.note kind pid)) (fun _=>source)

noncomputable def oldShape (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WG.M α)
    (frame : SameView StagedEntry.view body) : Shape (liftWGObserver
      (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? (HandshakeCausal.call kind pid body))) := by
  rw [HandshakeEffects.old_call]
  exact callbackShape kind pid _ (.native (.quiet body frame))

noncomputable def oldMetadataShape (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WG.M α)
    (source : PeerMetadata.Shape body) : Shape (liftWGObserver
      (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? (HandshakeCausal.call kind pid body))) := by
  rw [HandshakeEffects.old_call]
  exact callbackShape kind pid _ (.native (.metadata body source))

theorem session_source (pid : PeerId) : CausalJournal.session pid =
    receiptWGObserved
      (receiptWGObserved (liftWGPrefix (beginSession pid)) (fun r=>Event.old (.responder (.session pid r))))
      (fun r=>Event.exchange (.session pid r)) := by
  unfold CausalJournal.session ExchangeJoint.session CausalJournal.state Journal.session Responder.DriverCuts.session
  rw [ExchangeCausalSession.focus_receipt,ExchangeCausalSession.focus_receipt]
  rfl

noncomputable def sessionShape (pid : PeerId) : Shape (liftWGObserver (CausalJournal.session pid)) := by
  rw [session_source]
  apply receiptShape
  · apply receiptShape
    · exact .native (.metadata _ (PeerMetadata.sessionShape pid))
    · exact fun _=>.native (.oldSession _ _)
  · exact fun _=>.native (.exchange _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
