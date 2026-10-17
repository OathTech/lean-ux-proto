import Leanux.Proofs.WG.Config.AllowedLeaf

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

inductive ChildReparent : Device → Option NodeId → Slot → Device → Prop where
  | none (d : Device) (slot : Slot) : ChildReparent d none slot d
  | some (d : Device) (id : NodeId) (n : AipNode) (slot : Slot)
      (resident : d.nodes[id]? = some n) :
      ChildReparent d (some id) slot (writeNode d id { n with parent := slot })

def reparentSibling (sibling : Option NodeId) (slot : Slot) : WG.M Unit := do
  if ← branch .removeSiblingExists sibling.isSome then
    if let some c := sibling then reparentNode c slot

theorem reparentSibling_returns {d final : Device} {sibling : Option NodeId} {slot : Slot}
    (ready : ChildReparent d sibling slot final) :
    Returns (reparentSibling sibling slot) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  intro g ambient device
  let mark (value : Bool) := {ambient with steps := ambient.steps.push {
    decision := .removeSiblingExists, outcome := value, netRx := ambient.netRxSection}}
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases ready with
  | none =>
    refine ⟨(), g, mark false, ?_, device⟩
    simp [reparentSibling, branch, AmbientM.branch, mark]
    rfl
  | some id n _ resident =>
    refine ⟨(), {g with dev := some (writeNode d id {n with parent := slot})},
      mark true, ?_, rfl⟩
    simp [reparentSibling, reparentNode, aipLift, liftAip, getNode, setNode,
      getDev, modifyDev, device, resident, branch, AmbientM.branch, writeNode, mark]
    rfl

def collapseReadSibling (parent : NodeId) (bit : Nat) : WG.M (Option NodeId) := do
  _ ← branch .removeFreeParent true
  (← getNode parent).bitAt (1 - bit)

def collapseDeleteLeaf (id parent : NodeId) : WG.M AipNode := do
  freeNode id
  _ ← branch .removeNotFreeParent false
  getNode parent

def collapseFinish (sibling : Option NodeId) (parent : NodeId) (pn : AipNode) : WG.M (ForInStep Unit) := do
  reparentSibling sibling pn.parent
  slotSet pn.parent sibling
  freeNode parent
  pure (.yield ())

theorem collapse_source (id : NodeId) (n : AipNode) (parent : NodeId) (bit : Nat)
    (location : n.parent = .child parent bit) :
    leafAfterDecision id n true = (do
      let sibling ← collapseReadSibling parent bit
      let pn ← collapseDeleteLeaf id parent
      collapseFinish sibling parent pn) := by
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do
        (monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
          decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit) : WG.M Unit)
        pure value) := rfl
  simp [leafAfterDecision, collapseReadSibling, collapseDeleteLeaf, collapseFinish,
    reparentSibling, reparentNode, location, branchSource, bind_assoc]
  congr 1
  funext u
  congr 1
  funext pn
  congr 1
  funext sibling
  cases sibling <;> simp [bind_assoc]

theorem collapseReadSibling_returns (d : Device) (parent : NodeId) (bit : Nat) (pn : AipNode)
    (sibling : Option NodeId) (resident : d.nodes[parent]? = some pn)
    (read : pn.bit[1 - bit]? = some sibling) :
    Returns (collapseReadSibling parent bit) (fun w => w.dev = some d)
      (fun result w => result = sibling ∧ w.dev = some d) := by
  intro g ambient device
  let after := {ambient with steps := ambient.steps.push {
    decision := .removeFreeParent, outcome := true, netRx := ambient.netRxSection}}
  refine ⟨sibling, {g with dev := some d}, after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  simp [collapseReadSibling, aipLift, liftAip, getNode, getDev, modifyDev, device,
    resident, AipNode.bitAt, read, branch, AmbientM.branch, after]
  rfl

theorem collapseDeleteLeaf_returns (d : Device) (id parent : NodeId) (n pn : AipNode)
    (resident : d.nodes[id]? = some n) (parentRead : (d.nodes.erase id)[parent]? = some pn) :
    Returns (collapseDeleteLeaf id parent) (fun w => w.dev = some d)
      (fun result w => result = pn ∧ w.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient device
  let after := {ambient with steps := ambient.steps.push {
    decision := .removeNotFreeParent, outcome := false, netRx := ambient.netRxSection}}
  refine ⟨pn, {g with dev := some {d with nodes := d.nodes.erase id}}, after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  simp [collapseDeleteLeaf, aipLift, liftAip, freeNode, getNode, getDev, modifyDev,
    device, resident, parentRead, branch, AmbientM.branch, after]
  rfl

theorem collapseFinish_returns (d promoted linked : Device) (sibling : Option NodeId)
    (parent : NodeId) (pn remaining : AipNode)
    (reparent : ChildReparent d sibling pn.parent promoted)
    (write : SlotWrite promoted pn.parent sibling linked)
    (resident : linked.nodes[parent]? = some remaining) :
    Returns (collapseFinish sibling parent pn) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
  unfold collapseFinish
  refine returns_bind _ _ (reparentSibling_returns reparent) ?_
  intro u
  refine returns_bind _ _ (slotSet_returns_of_write write) ?_
  intro u
  refine returns_bind _ _ (freeNode_returns linked parent remaining resident) ?_
  intro u w ambient device
  exact ⟨.yield (), w, ambient, rfl, rfl, device⟩

theorem leafAfterDecision_true_returns (d promoted linked : Device) (id parent : NodeId)
    (bit : Nat) (n pn leaf pnAfter remaining : AipNode) (sibling : Option NodeId)
    (location : n.parent = .child parent bit)
    (parentRead : d.nodes[parent]? = some pn) (siblingRead : pn.bit[1 - bit]? = some sibling)
    (leafRead : d.nodes[id]? = some leaf)
    (parentAfter : (d.nodes.erase id)[parent]? = some pnAfter)
    (reparent : ChildReparent { d with nodes := d.nodes.erase id } sibling pnAfter.parent promoted)
    (write : SlotWrite promoted pnAfter.parent sibling linked)
    (resident : linked.nodes[parent]? = some remaining) :
    Returns (leafAfterDecision id n true) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
  rw [collapse_source id n parent bit location]
  refine returns_bind _ _ (collapseReadSibling_returns d parent bit pn sibling parentRead siblingRead) ?_
  intro read w ambient pre
  obtain ⟨value, device⟩ := pre
  subst read
  have tail : Returns (do let p ← collapseDeleteLeaf id parent; collapseFinish sibling parent p)
      (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
    refine returns_bind _ _ (collapseDeleteLeaf_returns d id parent leaf pnAfter leafRead parentAfter) ?_
    intro p w ambient pre
    obtain ⟨value, device⟩ := pre
    subst p
    exact collapseFinish_returns _ promoted linked sibling parent pnAfter remaining reparent write resident w ambient device
  exact tail w ambient device

theorem removeNodeSource_leaf_collapse (d detached promoted linked : Device) (id parent : NodeId)
    (bit : Nat) (n pn leaf pnAfter remaining : AipNode) (sibling : Option NodeId)
    (shape : n.bit = #[none, none]) (location : n.parent = .child parent bit)
    (unlink : SlotWrite (writeNode d id { n with peer := none }) n.parent none detached)
    (choice : ParentChoice detached n.parent true)
    (parentRead : detached.nodes[parent]? = some pn) (siblingRead : pn.bit[1 - bit]? = some sibling)
    (leafRead : detached.nodes[id]? = some leaf)
    (parentAfter : (detached.nodes.erase id)[parent]? = some pnAfter)
    (reparent : ChildReparent { detached with nodes := detached.nodes.erase id } sibling pnAfter.parent promoted)
    (write : SlotWrite promoted pnAfter.parent sibling linked)
    (resident : linked.nodes[parent]? = some remaining) :
    Returns (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
  rw [leaf_source id n shape]
  refine returns_bind _ _ (leafBeforeParent_returns d detached id n unlink) ?_
  intro u
  refine returns_bind _ _ (leafParentDecision_returns choice) ?_
  intro collapse w ambient pre
  obtain ⟨rfl, device⟩ := pre
  exact leafAfterDecision_true_returns detached promoted linked id parent bit n pn leaf pnAfter remaining
    sibling location parentRead siblingRead leafRead parentAfter reparent write resident w ambient device

end Leanux.Proofs.WG.Config
