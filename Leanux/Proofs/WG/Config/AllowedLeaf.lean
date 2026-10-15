import Leanux.Proofs.WG.Config.AllowedStructural

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def leafBeforeParent (id : NodeId) (n : AipNode) : M Unit := do
  setNode id { n with peer := none }
  _ ← branch .removeHasBit0 false
  _ ← branch .removeChildExists false
  slotSet n.parent none
  _ ← branch .removeLeafBit0 true
  _ ← branch .removeLeafBit1 true
  pure ()

def leafParentDecision (slot : Slot) : M Bool := do
  match slot with
  | .child parent _ =>
    _ ← branch .removeParentIsNode true
    branch .removeParentNoPeer (← getNode parent).peer.isNone
  | _ =>
    _ ← branch .removeParentIsNode false
    pure false

def leafAfterDecision (id : NodeId) (n : AipNode) (freeParent : Bool) : M (ForInStep Unit) := do
  let mut sibling : Option NodeId := none
  if ← branch .removeFreeParent freeParent then
    let .child parent bit := n.parent | do
      invariant "free_parent without a parent node"
      return .yield ()
    sibling ← (← getNode parent).bitAt (1 - bit)
  freeNode id
  if ← branch .removeNotFreeParent !freeParent then return .yield ()
  let .child parent _ := n.parent | do
    invariant "free_parent without a parent node"
    return .yield ()
  let pn ← getNode parent
  if ← branch .removeSiblingExists sibling.isSome then
    if let some c := sibling then setNode c { (← getNode c) with parent := pn.parent }
  slotSet pn.parent sibling
  freeNode parent
  return .yield ()

theorem leaf_source (id : NodeId) (n : AipNode) (shape : n.bit = #[none, none]) :
    removeNodeSource id n = (do
      leafBeforeParent id n
      let collapse ← leafParentDecision n.parent
      leafAfterDecision id n collapse) := by
  cases parent : n.parent <;> simp [removeNodeSource, leafBeforeParent, leafParentDecision, leafAfterDecision,
    AipNode.bitAt, shape, parent, branch, bind_assoc]
  repeat (first | rfl | (congr 1; funext u))

theorem leafBeforeParent_returns (d linked : Device) (id : NodeId) (n : AipNode)
    (write : SlotWrite (writeNode d id { n with peer := none }) n.parent none linked) :
    Returns (leafBeforeParent id n) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some linked) := by
  have hw := (returns_iff _ _ _).mp (slotSet_returns_of_write write)
  rw [returns_iff]
  mvcgen [leafBeforeParent, branch, setNode, modifyDev, modifyK, hw]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]
  all_goals exact hw _ (by assumption)

theorem leafAfterDecision_false_returns (d : Device) (id : NodeId) (n remaining : AipNode)
    (resident : d.nodes[id]? = some remaining) :
    Returns (leafAfterDecision id n false) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some { d with nodes := d.nodes.erase id }) := by
  rw [returns_iff]
  simp [leafAfterDecision, branch, bind_assoc]
  mvcgen [freeNode, getNode, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

inductive ParentChoice : Device → Slot → Bool → Prop where
  | root4 (d : Device) : ParentChoice d .root4 false
  | root6 (d : Device) : ParentChoice d .root6 false
  | child (d : Device) (parent : NodeId) (bit : Nat) (pn : AipNode)
      (resident : d.nodes[parent]? = some pn) :
      ParentChoice d (.child parent bit) pn.peer.isNone

theorem leafParentDecision_returns {d : Device} {slot : Slot} {collapse : Bool}
    (choice : ParentChoice d slot collapse) :
    Returns (leafParentDecision slot) (fun w => w.k.wg = some d)
      (fun result w => result = collapse ∧ w.k.wg = some d) := by
  cases choice <;> rw [returns_iff]
  all_goals mvcgen [leafParentDecision, branch, getNode, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem removeNodeSource_leaf_no_collapse (d linked : Device) (id : NodeId) (n : AipNode)
    (shape : n.bit = #[none, none])
    (write : SlotWrite (writeNode d id { n with peer := none }) n.parent none linked)
    (choice : ParentChoice linked n.parent false)
    (remaining : AipNode) (resident : linked.nodes[id]? = some remaining) :
    Returns (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some { linked with nodes := linked.nodes.erase id }) := by
  rw [leaf_source id n shape]
  refine returns_bind _ _ (leafBeforeParent_returns d linked id n write) ?_
  intro u
  refine returns_bind _ _ (leafParentDecision_returns choice) ?_
  intro result w pre
  obtain ⟨rfl, device⟩ := pre
  exact leafAfterDecision_false_returns linked id n remaining resident w device

end Leanux.Proofs.WG.Config
