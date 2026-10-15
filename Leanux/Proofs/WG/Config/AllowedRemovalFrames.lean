import Leanux.Proofs.WG.Config.AllowedRemoval
import Leanux.Proofs.WG.Config.AllowedRemovalModel

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem slotWrite_frame {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) : withoutTrie final = withoutTrie d := by
  cases write <;> rfl

theorem childReparent_frame {d final : Device} {child : Option NodeId} {slot : Slot}
    (write : ChildReparent d child slot final) : withoutTrie final = withoutTrie d := by
  cases write <;> rfl

theorem nodeRemoval_frame {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : withoutTrie final = withoutTrie d := by
  cases step with
  | branching left right shape => rfl
  | unary child c side shape childRead linked write remaining resident =>
    simpa only [withoutTrie, writeNode] using slotWrite_frame write
  | leaf linked shape write choice remaining resident => simpa only [withoutTrie, writeNode] using slotWrite_frame write
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write resident =>
    have h1 := slotWrite_frame write
    have h2 := childReparent_frame reparent
    have h3 := slotWrite_frame unlink
    simpa only [withoutTrie, writeNode] using h1.trans (h2.trans h3)

theorem nodeRemoval_peers {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : final.peers = d.peers := by
  simpa only [withoutTrie] using congrArg Device.peers (nodeRemoval_frame step)

theorem nodeRemoval_seq {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : final.peerAllowedips.seq = d.peerAllowedips.seq := by
  simpa only [withoutTrie] using congrArg (fun d => d.peerAllowedips.seq) (nodeRemoval_frame step)

theorem erasePeerList_refcount (ids : List NodeId) (p : Peer) :
    (erasePeerList ids p).refcount = p.refcount := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih => exact ih (eraseListedPeer id p)

theorem erasePeerList_identity (ids : List NodeId) (p : Peer) :
    (erasePeerList ids p).internalId = p.internalId := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih => exact ih (eraseListedPeer id p)

theorem removalRun_running {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : final.running = d.running := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have h1 := congrArg Device.running (nodeRemoval_frame step)
    have h2 := congrArg Device.running (deleteListedNodes_withoutPeers id d d.peers.toList)
    simpa only [withoutTrie, withoutPeers] using h1.trans h2

theorem removalEffect_running {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : final.running = d.running := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest =>
    have h := removalRun_running steps
    exact h

theorem removalRun_seq {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : final.peerAllowedips.seq = d.peerAllowedips.seq := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih, nodeRemoval_seq step, deleteListedNodes_allowedips]

theorem writeNode_owner_frame (d : Device) (id tracked : NodeId) (old n : AipNode)
    (resident : d.nodes[id]? = some old) (owner : n.peer = old.peer) :
    nodeOwner (writeNode d id n) tracked = nodeOwner d tracked := by
  rw [writeNode_owner]
  by_cases same : tracked = id
  · subst tracked; simp [nodeOwner, resident, owner]
  · simp [same]

theorem slotWrite_owner {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) (tracked : NodeId) :
    nodeOwner final tracked = nodeOwner d tracked := by
  cases write with
  | root4 => rfl
  | root6 => rfl
  | child parent bit n value resident valid shape =>
    exact writeNode_owner_frame d parent tracked n _ resident rfl

theorem childReparent_owner {d final : Device} {child : Option NodeId} {slot : Slot}
    (write : ChildReparent d child slot final) (tracked : NodeId) :
    nodeOwner final tracked = nodeOwner d tracked := by
  cases write with
  | none => rfl
  | some id n slot resident => exact writeNode_owner_frame d id tracked n _ resident rfl

theorem deleteListedNodes_owner (d : Device) (id tracked : NodeId) :
    nodeOwner (deleteListedNodes id d d.peers.toList) tracked = nodeOwner d tracked := by
  have nodes := congrArg Device.nodes (deleteListedNodes_withoutPeers id d d.peers.toList)
  simpa only [withoutPeers, nodeOwner] using congrArg (fun nodes => nodes[tracked]?.bind AipNode.peer) nodes

theorem removalRun_metadata {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : removalMetadata final = removalMetadata d := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have hn := congrArg removalMetadata (nodeRemoval_frame step)
    have hl := congrArg removalMetadata (deleteListedNodes_withoutPeers id d d.peers.toList)
    simpa only [removalMetadata, withoutTrie, withoutPeers] using hn.trans hl

theorem removalEffect_metadata {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : removalMetadata final = removalMetadata d := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest =>
    have h := removalRun_metadata steps
    exact h

theorem removalRun_queues {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : removalQueues final = removalQueues d := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have hn := congrArg removalQueues (nodeRemoval_frame step)
    have hl := congrArg removalQueues (deleteListedNodes_withoutPeers id d d.peers.toList)
    simpa only [removalQueues, withoutTrie, withoutPeers] using hn.trans hl

theorem removalEffect_queues {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : removalQueues final = removalQueues d := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest => have h := removalRun_queues steps; exact h

theorem erasePeerList_exceptList (ids : List NodeId) (p : Peer) :
    { erasePeerList ids p with allowedipsList := [] } = { p with allowedipsList := [] } := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih => exact ih (eraseListedPeer id p)

end Leanux.Proofs.WG.Config
