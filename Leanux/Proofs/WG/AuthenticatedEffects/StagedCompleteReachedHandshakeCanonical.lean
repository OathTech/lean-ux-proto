import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumerCanonical

/-! Canonical witnesses follow the unchanged handshake branches, wrappers
and callback order. No whole-worker source premise is accepted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open RetirementSecurity HandshakeSecurity Origins.HandshakeSources

elab "handshake_source_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a handshake source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not an observed WG source"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"


noncomputable def derivedShape (pid : PeerId) : Shape (liftWGObserver (TimerEffects.derivedWith effects pid)) :=
  .leaf (Consume.Leaf.discardShape _ (Consume.Leaf.modifyShape .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS))

macro "handshake_source_step" : tactic => `(tactic| first
  | (handshake_source_head CausalScope.scope; apply scopeShape)
  | (handshake_source_head receiptWGObserved; apply receiptShape; rotate_left; exact fun _=>.native (.exchange _))
  | (handshake_source_head HandshakeWorker.callback; apply callbackShape)
  | (handshake_source_head HandshakeWorker.old
     apply oldMetadataShape
     first
       | (metadata_source_head createResponse; exact PeerMetadata.createResponseShape _)
       | (metadata_source_head addMacToPacket; exact PeerMetadata.addMacShape _ _)
       | (metadata_source_head timersAnyAuthenticatedPacketSent; exact PeerMetadata.sentShape _)
       | (metadata_source_head timersAnyAuthenticatedPacketReceived; exact PeerMetadata.receivedShape _)
       | (metadata_source_head setPeerEndpointFromSkb; exact PeerMetadata.endpointShape _ _)
       | (metadata_source_head timersHandshakeComplete; exact PeerMetadata.completeShape _ _)
       | (metadata_update_head; apply PeerMetadata.updateShape; intro p; exact ⟨rfl,rfl,rfl⟩))
  | (handshake_source_head CausalJournal.session; exact sessionShape _)
  | (handshake_source_head Driver.keepaliveObserved; exact .child (.keepalive _))
  | (handshake_source_head ProtocolSocket.observed; exact .native (.protocol _ _))
  | (handshake_source_head CookieSocket.observed; exact cookieShape _ _ _)
  | (handshake_source_head NestedPeerRelease.admitInitiationWith; exact admittedInitiationShape _)
  | (handshake_source_head NestedPeerRelease.admitResponseWith; exact admittedResponseShape _)
  | (handshake_source_head NestedPeerRelease.cookieObserved; exact consumedCookieShape _)
  | (handshake_source_head TimerEffects.derivedWith; exact derivedShape _)
  | (handshake_source_head TimerEffects.traversalWith; exact .leaf (Consume.Leaf.traversalShape _))
  | (handshake_source_head StagedDisposal.Decoration.release; exact .child (.release _))
  | (handshake_source_head captureWGRun; exact .native (.capturedMetadata _ (PeerMetadata.validateCookieShape _ _ _)))
  | (handshake_source_head liftWGPrefix
     refine .native (.metadata _ ?_)
     repeat' first
       | (metadata_source_head Cookies.loadPhase; exact PeerMetadata.loadShape)
       | metadata_source_step)
  | (handshake_source_head Pure.pure; exact .pure _)
  | (handshake_source_head Bind.bind; apply stateBindShape)
  | (handshake_source_head ite; apply conditionalShape)
  | maintenance_join_let
  | maintenance_join_use
  | intro value
  | (dsimp +failIfUnchanged only)
  | split)

noncomputable def responseSource (mac : HandshakeMac) (pid : PeerId) :
    Shape (liftWGObserver (responseWith (CompleteHandshakeWorker.make CausalJournal.session
      (Driver.keepaliveObserved hooks) mac) pid)) := by
  unfold responseWith CompleteHandshakeWorker.make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' handshake_source_step

noncomputable def afterMacSource (mac : HandshakeMac) (bytes : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Shape (liftWGObserver (afterMacWith (CompleteHandshakeWorker.make CausalJournal.session
      (Driver.keepaliveObserved hooks) mac) bytes src loaded state)) := by
  unfold afterMacWith CompleteHandshakeWorker.make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (handshake_source_head responseWith; exact responseSource _ _)
    | handshake_source_step

noncomputable def receiveSource (bytes : Key) (src : SkbSource) :
    Shape (liftWGObserver (CookieConsumption.receiveWith
      (NestedPeerRelease.cookieObserved CompleteConsumers.nested Event.cookieConsumed)
      (CompleteHandshakeWorker.make CausalJournal.session (Driver.keepaliveObserved hooks)) bytes src)) := by
  unfold CookieConsumption.receiveWith
  repeat' first
    | (handshake_source_head afterMacWith; exact afterMacSource _ _ _ _ _)
    | handshake_source_step

noncomputable def source : Shape (liftWGObserver (Driver.handshakeObserved hooks)) := by
  change Shape (liftWGObserver (CausalJournal.handshake CausalJournal.session (Driver.keepaliveObserved hooks)))
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (handshake_source_head CookieConsumption.receiveWith; exact receiveSource _ _)
    | handshake_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
