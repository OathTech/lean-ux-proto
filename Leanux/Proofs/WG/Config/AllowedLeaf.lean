import Leanux.Proofs.WG.Config.AllowedStructural

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def leafBeforeParent (id : NodeId) (n : AipNode) : WG.M Unit := do
  setNode id { n with peer := none }
  _ ← branch .removeHasBit0 false
  _ ← branch .removeChildExists false
  slotSet n.parent none
  _ ← branch .removeLeafBit0 true
  _ ← branch .removeLeafBit1 true
  pure ()

def leafParentDecision (slot : Slot) : WG.M Bool := do
  match slot with
  | .child parent _ =>
    _ ← branch .removeParentIsNode true
    branch .removeParentNoPeer (← getNode parent).peer.isNone
  | _ =>
    _ ← branch .removeParentIsNode false
    pure false

def leafAfterDecision (id : NodeId) (n : AipNode) (freeParent : Bool) : WG.M (ForInStep Unit) := do
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
  funext g ambient
  cases parent : n.parent <;> simp [removeNodeSource, leafBeforeParent, leafParentDecision, leafAfterDecision,
    AipNode.bitAt, shape, parent, branch, AmbientM.branch, bind_assoc]
  repeat (first | rfl | (congr 1; funext u))

theorem leafBeforeParent_returns (d linked : Device) (id : NodeId) (n : AipNode)
    (write : SlotWrite (writeNode d id { n with peer := none }) n.parent none linked) :
    Returns (leafBeforeParent id n) (fun w => w.dev = some d)
      (fun _ w => w.dev = some linked) := by
  have hbranch (site : Decision) (value : Bool) (entry : Device) :
      Returns (branch site value : WG.M Bool) (fun g => g.dev = some entry)
        (fun _ g => g.dev = some entry) := by
    intro g ambient device
    refine ⟨value, g, {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}}, ?_, device⟩
    rfl
  unfold leafBeforeParent
  refine returns_bind _ _ (setNode_returns d id {n with peer := none}) ?_
  intro _
  refine returns_bind _ _ (hbranch .removeHasBit0 false _) ?_
  intro _
  refine returns_bind _ _ (hbranch .removeChildExists false _) ?_
  intro _
  refine returns_bind _ _ (slotSet_returns_of_write write) ?_
  intro _
  refine returns_bind _ _ (hbranch .removeLeafBit0 true linked) ?_
  intro _
  refine returns_bind _ _ (hbranch .removeLeafBit1 true linked) ?_
  intro _ g ambient device
  exact ⟨(), g, ambient, rfl, device⟩

theorem leafAfterDecision_false_returns (d : Device) (id : NodeId) (n remaining : AipNode)
    (resident : d.nodes[id]? = some remaining) :
    Returns (leafAfterDecision id n false) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ w.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let after := mark (mark ambient .removeFreeParent false) .removeNotFreeParent true
  refine ⟨.yield (), {g with dev := some {d with nodes := d.nodes.erase id}}, after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  simp [leafAfterDecision, aipLift, liftAip, freeNode, getNode, getDev, modifyDev,
    device, resident, branch, AmbientM.branch, after, mark]
  rfl

inductive ParentChoice : Device → Slot → Bool → Prop where
  | root4 (d : Device) : ParentChoice d .root4 false
  | root6 (d : Device) : ParentChoice d .root6 false
  | child (d : Device) (parent : NodeId) (bit : Nat) (pn : AipNode)
      (resident : d.nodes[parent]? = some pn) :
      ParentChoice d (.child parent bit) pn.peer.isNone

theorem leafParentDecision_returns {d : Device} {slot : Slot} {collapse : Bool}
    (choice : ParentChoice d slot collapse) :
    Returns (leafParentDecision slot) (fun w => w.dev = some d)
      (fun result w => result = collapse ∧ w.dev = some d) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases choice with
  | root4 =>
    refine ⟨false, g, mark ambient .removeParentIsNode false, ?_, rfl, device⟩
    simp [leafParentDecision, branch, AmbientM.branch, mark]
    rfl
  | root6 =>
    refine ⟨false, g, mark ambient .removeParentIsNode false, ?_, rfl, device⟩
    simp [leafParentDecision, branch, AmbientM.branch, mark]
    rfl
  | child parent bit pn resident =>
    refine ⟨pn.peer.isNone, {g with dev := some d},
      mark (mark ambient .removeParentIsNode true) .removeParentNoPeer pn.peer.isNone, ?_, rfl, rfl⟩
    simp [leafParentDecision, aipLift, liftAip, getNode, getDev, modifyDev,
      device, resident, branch, AmbientM.branch, mark]
    rfl

theorem removeNodeSource_leaf_no_collapse (d linked : Device) (id : NodeId) (n : AipNode)
    (shape : n.bit = #[none, none])
    (write : SlotWrite (writeNode d id { n with peer := none }) n.parent none linked)
    (choice : ParentChoice linked n.parent false)
    (remaining : AipNode) (resident : linked.nodes[id]? = some remaining) :
    Returns (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ w.dev = some { linked with nodes := linked.nodes.erase id }) := by
  rw [leaf_source id n shape]
  refine returns_bind _ _ (leafBeforeParent_returns d linked id n write) ?_
  intro u
  refine returns_bind _ _ (leafParentDecision_returns choice) ?_
  intro result w ambient pre
  obtain ⟨rfl, device⟩ := pre
  exact leafAfterDecision_false_returns linked id n remaining resident w ambient device

end Leanux.Proofs.WG.Config
