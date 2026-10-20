import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakeSource

/-! Literal initiation, response and cookie consumer trees retain their original acceptance captures, nested counted repayments and final receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open RetirementSecurity NestedPeerRelease

theorem capture_source (body : WGPrefix Event α) : liftWGObserver (captureWGObserved body) = (do
    let before←liftPrefix (get : Leanux.M World)
    let value←liftWGObserver body
    let after←liftPrefix (get : Leanux.M World)
    pure ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩) := by
  funext w h
  change runPrefix (liftWGObserver (captureWGObserved body)) w h=runPrefix (do
    let value←liftWGObserver body
    let after←liftPrefix (get : Leanux.M World)
    pure ⟨value,w.wg,after.wg,w.ambient,after.ambient⟩) w h
  rw [liftWGObserver_run,runWGPrefix_captureWGObserved,runPrefix_bind,liftWGObserver_run]
  cases performed : runWGPrefix body w.wg w.ambient h with
  | mk result last=>cases result with
    | error stop=>rfl
    | ok out=>rcases out with ⟨⟨value,v⟩,b⟩;rfl

noncomputable def captureShape (body : WGPrefix Event α) (source : Shape (liftWGObserver body)) :
    Shape (liftWGObserver (captureWGObserved body)) := by
  rw [capture_source]
  exact .bind (.leaf (.native (.base (.basic .world)))) fun before=>
    .bind source fun value=>.bind (.leaf (.native (.base (.basic .world)))) fun after=>
      .pure (⟨value,before.wg,after.wg,before.ambient,after.ambient⟩ : WGRunWitness α)

noncomputable def updateThenShape (pid : PeerId) (f : Peer→Peer) (next : Unit→WGPrefix Event α)
    (fields : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
    (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (liftWGPrefix (getPeer pid) >>= fun p=>liftWGPrefix (setPeer pid (f p)) >>= next)) := by
  rw [←bind_assoc,←Queued.lift_bind,liftWGObserver_bind]
  exact .bind (.native (.metadata _ (PeerMetadata.updateShape pid f fields))) tail

open Lean Meta Elab Tactic in
elab "consumer_source_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a consumer shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless body.getAppFn.constName? == some name do throwError "different source head"

open Lean Meta Elab Tactic in
elab "consumer_wg_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a consumer shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  unless body.isAppOf ``liftWGPrefix do throwError "not a native lift"
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless body.getAppArgs.back!.consumeMData.headBeta.getAppFn.constName? == some name do throwError "different native head"

open Lean Meta Elab Tactic in
elab "consumer_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a consumer shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do throwError "not a bind"
  let args := body.getAppArgs
  let head := args[args.size-2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix && head.getAppArgs.back!.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ tail _ := args.back!.consumeMData | throwError "not a saved peer"
  unless tail.isAppOf ``Bind.bind do throwError "not a write continuation"
  let parts := tail.getAppArgs
  let write := parts[parts.size-2]!.consumeMData
  unless write.isAppOf ``liftWGPrefix && write.getAppArgs.back!.isAppOf ``setPeer do throwError "not a peer write"

macro "consumer_source_step" : tactic => `(tactic| first
  | dsimp (config := {failIfUnchanged := true}) only
  | (consumer_update_head; apply updateThenShape; first | exact fun _=>⟨rfl,rfl,rfl⟩ | intro value)
  | (consumer_wg_head mixPrecomputedDh; exact .native (.metadata _ (PeerMetadata.precomputedShape _ _)))
  | (consumer_wg_head messageDecrypt; exact .native (.metadata _ (PeerMetadata.decryptShape _ _ _)))
  | (consumer_wg_head indexLookup; exact .native (.lookup _ (Lookup.canonical _ _)))
  | (consumer_wg_head pubkeyLookup; exact .native (.lookup _ (Lookup.pubkeyShape _)))
  | (consumer_wg_head initiationAuthFront; exact .native (.metadata _ (PeerMetadata.authFrontShape _)))
  | (consumer_wg_head cookieAuthFront; exact .native (.metadata _ (PeerMetadata.cookieAuthShape _ _)))
  | (consumer_wg_head initiationAcceptedContinue; exact .native (.metadata _ (PeerMetadata.acceptedInitiationShape _ _)))
  | (consumer_wg_head responseAcceptedContinue; exact .native (.metadata _ (PeerMetadata.acceptedResponseShape _ _)))
  | (consumer_source_head HandshakeSecurity.StagedDisposal.Decoration.release; exact .child (.release _))
  | (consumer_source_head liftWGPrefix
     refine .native (.metadata _ ?_)
     repeat' first | metadata_source_step | unfold messageDecrypt | unfold mixPrecomputedDh)
  | (consumer_source_head Pure.pure; exact .pure _)
  | (consumer_source_head Bind.bind; apply stateBindShape)
  | (consumer_source_head ite; apply conditionalShape)
  | maintenance_join_let
  | maintenance_join_use
  | intro value
  | split)

noncomputable def initiationOutShape (peer ret : Option PeerId) : Shape
    (liftWGObserver (initiationOutWith CompleteConsumers.nested peer ret)) := by
  unfold initiationOutWith
  simp only [CompleteConsumers.nested,observedOps]
  repeat' consumer_source_step

noncomputable def initiationTailShape (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) : Shape
    (liftWGObserver (initiationTailWith CompleteConsumers.nested msg e ck hash peer pid)) := by
  unfold initiationTailWith
  -- The tree is independent of the closed delay arithmetic; the invocation keeps its original value.
  generalize (NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64) = delay
  simp only [CompleteConsumers.nested,observedOps]
  repeat' first
    | (consumer_source_head initiationOutWith; exact initiationOutShape _ _)
    | consumer_source_step

noncomputable def initiationCheckShape (msg : Key) : Shape
    (liftWGObserver (initiationCheckWith CompleteConsumers.nested msg)) := by
  unfold initiationCheckWith
  simp only [CompleteConsumers.nested,observedOps]
  repeat' first
    | (consumer_source_head initiationOutWith; exact initiationOutShape _ _)
    | (consumer_source_head initiationTailWith; exact initiationTailShape _ _ _ _ _ _)
    | consumer_source_step

noncomputable def responseTailShape (msg : Key) (identity : StaticIdentity) (pid : PeerId) : Shape
    (liftWGObserver (responseTailWith CompleteConsumers.nested msg identity pid)) := by
  unfold responseTailWith
  simp only [CompleteConsumers.nested,observedOps]
  repeat' consumer_source_step

noncomputable def responseCheckShape (msg : Key) : Shape
    (liftWGObserver (responseCheckWith CompleteConsumers.nested msg)) := by
  unfold responseCheckWith
  simp only [CompleteConsumers.nested,observedOps]
  repeat' first
    | (consumer_source_head responseTailWith; exact responseTailShape _ _ _)
    | consumer_source_step

noncomputable def cookieCheckShape (msg : Key) : Shape
    (liftWGObserver (cookieWith CompleteConsumers.nested msg)) := by
  unfold cookieWith cookieAfterWith
  simp only [CompleteConsumers.nested,observedOps]
  repeat' consumer_source_step

noncomputable def admittedInitiationShape (mac : HandshakeMac) : Shape (liftWGObserver
    (admitInitiationWith CompleteConsumers.nested ConsumerObserved.admission mac)) := by
  unfold admitInitiationWith
  repeat' first
    | (consumer_source_head captureWGObserved; exact captureShape _ (initiationCheckShape _))
    | (consumer_source_head emitStatePrefix; exact .native (.admission _))
    | consumer_source_step

noncomputable def admittedResponseShape (mac : HandshakeMac) : Shape (liftWGObserver
    (admitResponseWith CompleteConsumers.nested ConsumerObserved.admission mac)) := by
  unfold admitResponseWith
  repeat' first
    | (consumer_source_head captureWGObserved; exact captureShape _ (responseCheckShape _))
    | (consumer_source_head emitStatePrefix; exact .native (.admission _))
    | consumer_source_step

noncomputable def consumedCookieShape (bytes : Key) : Shape (liftWGObserver
    (NestedPeerRelease.cookieObserved CompleteConsumers.nested Event.cookieConsumed bytes)) := by
  unfold NestedPeerRelease.cookieObserved
  exact receiptShape _ _ (cookieCheckShape bytes) (fun _=>.native (.cookieReceipt _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
