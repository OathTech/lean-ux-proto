import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutingFrames

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Routing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def aipShape (action : AipM α) : PeerMetadata.Shape (liftAip action) := by
  apply PeerMetadata.Shape.access
  simp only [liftAip,getDev,invariant]
  repeat' access_source_step

open Lean Meta Elab Tactic in
elab "routing_source_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a routing source shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless action.getAppFn.constName? == some name do throwError "different native source head"

open Lean Meta Elab Tactic in
elab "routing_source_split" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a routing source shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``ite || action.isAppOf ``dite || (← matchMatcherApp? action).isSome do
    throwError "not a native source branch"
  evalTactic (← `(tactic| split))

macro "routing_source_step" : tactic => `(tactic| first
  | dsimp (config := {failIfUnchanged := true}) only
  | (routing_source_head listDel; exact .delete _)
  | (routing_source_head liftAip; exact .metadata (aipShape _))
  | (routing_source_head liftM; exact .metadata (aipShape _))
  | (routing_source_head getPeer; exact .metadata (.access (PeerMetadata.readShape _)))
  | (routing_source_head listAddTail; apply Shape.metadata; unfold listAddTail; apply PeerMetadata.updateShape; intro p; exact ⟨rfl,rfl,rfl⟩)
  | (routing_source_head ForIn.forIn; apply listShape)
  | (routing_source_head ForIn.forIn; apply rangeShape)
  | (routing_source_head ite; apply conditionalShape)
  | routing_source_split
  | (solve | apply Shape.metadata; metadata_update_head; repeat' metadata_source_step)
  | (routing_source_head modifyDev; apply Shape.metadata; repeat' metadata_source_step)
  | (routing_source_head getDev; apply Shape.metadata; repeat' metadata_source_step)
  | (routing_source_head Pure.pure; exact .metadata (.access (.pure _)))
  | (routing_source_head Bind.bind; apply Shape.bind)
  | (solve | exact .metadata (.access (.ambient _)))
  | maintenance_intro
  | unfold getDev
  | unfold invariant
  | unfold unsupported
  | unfold WG.andM
  | unfold WG.orM
  | unfold branchCmp
  | unfold branch
  | unfold commonBits
  | unfold choose
  | unfold AipNode.bitAt)

noncomputable def addShape (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Shape (WG.add root bits key cidr peer) := by
  unfold WG.add
  repeat' routing_source_step

noncomputable def insertShape (family addr cidr : Nat) (pid : PeerId) : Shape (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first | (routing_source_head WG.add; exact addShape _ _ _ _ _) | routing_source_step

noncomputable def setShape (pid : PeerId) (ip : AllowedIpAttrs) : Shape (setAllowedip pid ip) := by
  unfold setAllowedip
  repeat' first | (routing_source_head WG.insert; exact insertShape _ _ _ _) | routing_source_step

noncomputable def removeParentShape (parent : NodeId) (sibling : Option NodeId) :
    Shape (AllowedIps.removeParentTail parent sibling) := by
  unfold AllowedIps.removeParentTail
  repeat' routing_source_step

noncomputable def removeNodeShape (node : NodeId) : Shape (AllowedIps.removeNodeBody node) := by
  unfold AllowedIps.removeNodeBody
  repeat' first
    | (routing_source_head AllowedIps.removeParentTail; exact removeParentShape _ _)
    | routing_source_step

noncomputable def removeStepShape (node : NodeId) : Shape (AllowedIps.removeStep node) := by
  unfold AllowedIps.removeStep
  repeat' first
    | (routing_source_head AllowedIps.removeNodeBody; exact removeNodeShape _)
    | routing_source_step

noncomputable def removeShape (pid : PeerId) : Shape (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  repeat' first
    | (routing_source_head AllowedIps.removeStep; exact removeStepShape _)
    | routing_source_step

noncomputable def rootRemoveShape (root : NodeId) : Shape (rootRemovePeerLists root) := by
  unfold rootRemovePeerLists
  repeat' routing_source_step

noncomputable def freeShape : Shape WG.free := by
  unfold WG.free
  repeat' first | (routing_source_head rootRemovePeerLists; exact rootRemoveShape _) | routing_source_step

noncomputable def deadShape (pid : PeerId) : Shape (peerMakeDead pid) := by
  unfold peerMakeDead
  repeat' first | (routing_source_head removeByPeer; exact removeShape _) | routing_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Routing
