import Leanux.Proofs.WG.Config.AllowedRemovalEffects

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

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
