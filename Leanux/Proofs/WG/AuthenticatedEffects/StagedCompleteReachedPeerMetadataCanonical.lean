import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataFrames

/-! Concrete response creation, MAC and handshake timer witnesses expand their original source through atomic accesses and actual saved-peer metadata writes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def indexShape (action : IndexM α) : Access.Shape (liftIndex action) := by
  simp only [liftIndex,getDev,invariant]
  repeat' access_source_step

noncomputable def updateShape (pid : PeerId) (f : Peer → Peer)
    (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue) :
    Shape (getPeer pid >>= fun p=>setPeer pid (f p)) := by
  have last (p : Peer) : (setPeer pid (f p) >>= fun _=>pure ())=setPeer pid (f p) := by
    have unit : (fun _ : Unit=>pure () : Unit→WG.M Unit)=pure := by
      funext value
      cases value
      rfl
    rw [unit,bind_pure]
  simpa only [last] using Shape.update pid f (fun _=>pure ()) same (fun _=>.access (.pure ()))

noncomputable def timerDeleteShape (pid : PeerId) (timer : PeerTimer) : Shape (delTimer pid timer) := by
  unfold delTimer
  apply updateShape
  intro p
  cases timer <;> exact ⟨rfl,rfl,rfl⟩

open Lean Meta Elab Tactic in
elab "metadata_source_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a metadata shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless action.getAppFn.constName? == some name do throwError "different native source head"

open Lean Meta Elab Tactic in
elab "metadata_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a metadata shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a source bind"
  let args := action.getAppArgs
  unless args[args.size-2]!.consumeMData.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ next _ := args.back!.consumeMData | throwError "not a saved-peer continuation"
  let next := next.consumeMData.headBeta
  if next.isAppOf ``setPeer then return
  unless next.isAppOf ``Bind.bind do throwError "not a saved-peer write bind"
  let parts := next.getAppArgs
  unless parts[parts.size-2]!.consumeMData.isAppOf ``setPeer do throwError "not a saved-peer write"

macro "metadata_source_step" : tactic => `(tactic| first
  | dsimp (config := {failIfUnchanged := true}) only
  | (metadata_update_head; apply Shape.update; · intro p; exact ⟨rfl,rfl,rfl⟩)
  | (metadata_update_head; apply updateShape; intro p; exact ⟨rfl,rfl,rfl⟩)
  | (metadata_source_head delTimer; exact timerDeleteShape _ _)
  | (metadata_source_head getPeer; exact .access (readShape _))
  | (metadata_source_head liftIndex; exact .access (indexShape _))
  | (metadata_source_head liftM; exact .access (indexShape _))
  | exact Shape.access (.pure _)
  | exact Shape.access .read
  | exact Shape.access (.ambient _)
  | (metadata_source_head modifyDev; apply Shape.access; apply Access.Shape.write; apply ReceiveFrames.device <;> intro d <;> rfl)
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split
  | unfold IndexOwner.peerDeref
  | unfold IndexOwner.peerWord
  | unfold getKeypair
  | unfold getDev
  | unfold invariant
  | unfold unsupported
  | unfold generatePublic
  | unfold messageEphemeral
  | unfold mixDh
  | unfold kdf
  | unfold kdfOut
  | unfold WG.andM
  | unfold WG.orM
  | unfold branchExpired
  | unfold birthdateTest)

noncomputable def createResponseShape (pid : PeerId) : Shape (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  repeat' metadata_source_step

noncomputable def addMacShape (pid : PeerId) (msg : Key) : Shape (addMacToPacket pid msg) := by
  unfold addMacToPacket
  repeat' metadata_source_step

noncomputable def sentShape (pid : PeerId) : Shape (timersAnyAuthenticatedPacketSent pid) :=
  timerDeleteShape pid .sendKeepalive

noncomputable def receivedShape (pid : PeerId) : Shape (timersAnyAuthenticatedPacketReceived pid) :=
  timerDeleteShape pid .newHandshake

noncomputable def completeShape (pid : PeerId) (site : HiddenSite) : Shape (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  repeat' metadata_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
