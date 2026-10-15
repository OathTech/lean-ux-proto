import Leanux.Proofs.WG.Config.AllowedRemovalEffects

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Missing nodes and resident nodes with no peer both have no owner. -/
def nodeOwner (d : Device) (id : NodeId) : Option PeerId :=
  d.nodes[id]?.bind AipNode.peer

theorem writeNode_owner (d : Device) (id tracked : NodeId) (n : AipNode) :
    nodeOwner (writeNode d id n) tracked = if tracked = id then n.peer else nodeOwner d tracked := by
  by_cases same : tracked = id <;> simp [nodeOwner, writeNode, Std.TreeMap.getElem?_insert, same, Ne.symm]

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

theorem clearNode_owner_none (d : Device) (id tracked : NodeId) (n : AipNode)
    (clear : tracked = id ∨ nodeOwner d tracked = none) :
    nodeOwner (writeNode d id { n with peer := none }) tracked = none := by
  rw [writeNode_owner]
  rcases clear with same | absent <;> simp_all

theorem eraseNode_owner_none (d : Device) (id tracked : NodeId)
    (clear : tracked = id ∨ nodeOwner d tracked = none) :
    nodeOwner { d with nodes := d.nodes.erase id } tracked = none := by
  by_cases same : tracked = id <;> simp_all [nodeOwner, Std.TreeMap.getElem?_erase, Ne.symm]

theorem nodeRemoval_owner_none {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) (tracked : NodeId)
    (clear : tracked = id ∨ nodeOwner d tracked = none) : nodeOwner final tracked = none := by
  have cleared := clearNode_owner_none d id tracked n clear
  cases step with
  | branching left right shape => exact cleared
  | unary child c side shape childRead linked write remaining resident =>
    apply eraseNode_owner_none
    right
    rw [slotWrite_owner write, writeNode_owner_frame _ child tracked c { c with parent := n.parent } childRead rfl]
    exact cleared
  | leaf linked shape write choice remaining resident =>
    apply eraseNode_owner_none
    right
    rw [slotWrite_owner write]
    exact cleared
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write resident =>
    apply eraseNode_owner_none
    right
    rw [slotWrite_owner write, childReparent_owner reparent]
    apply eraseNode_owner_none
    right
    rw [slotWrite_owner unlink]
    exact cleared

theorem deleteListedNodes_owner (d : Device) (id tracked : NodeId) :
    nodeOwner (deleteListedNodes id d d.peers.toList) tracked = nodeOwner d tracked := by
  have nodes := congrArg Device.nodes (deleteListedNodes_withoutPeers id d d.peers.toList)
  simpa only [withoutPeers, nodeOwner] using congrArg (fun nodes => nodes[tracked]?.bind AipNode.peer) nodes

theorem removalRun_owner_none {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) (tracked : NodeId)
    (clear : tracked ∈ ids ∨ nodeOwner d tracked = none) : nodeOwner final tracked = none := by
  induction steps with
  | nil d => simpa using clear
  | cons d id rest n next final read step tail ih =>
    apply ih
    rcases clear with member | absent
    · rcases List.mem_cons.mp member with same | member
      · right
        exact nodeRemoval_owner_none step tracked (Or.inl same)
      · exact Or.inl member
    · right
      apply nodeRemoval_owner_none step tracked
      right
      simpa only [deleteListedNodes_owner] using absent

theorem removalEffect_owner_none {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (tracked : NodeId)
    (clear : tracked ∈ ids ∨ nodeOwner d tracked = none) : nodeOwner final tracked = none := by
  cases ids with
  | nil => subst final; simpa using clear
  | cons id rest => exact removalRun_owner_none steps tracked clear

end Leanux.Proofs.WG.Config
