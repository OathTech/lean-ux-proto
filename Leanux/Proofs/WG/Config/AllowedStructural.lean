import Leanux.Proofs.WG.Config.AllowedRootRemoval

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def writeNode (d : Device) (id : NodeId) (n : AipNode) : Device :=
  { d with nodes := d.nodes.insert id n }

/-- Operational slot readiness and the exact write, including the parent's actual array. -/
inductive SlotWrite : Device → Slot → Option NodeId → Device → Prop where
  | root4 (d : Device) (value : Option NodeId) :
    SlotWrite d .root4 value { d with peerAllowedips := { d.peerAllowedips with root4 := value } }
  | root6 (d : Device) (value : Option NodeId) :
    SlotWrite d .root6 value { d with peerAllowedips := { d.peerAllowedips with root6 := value } }
  | child (d : Device) (parent : NodeId) (bit : Nat) (n : AipNode) (value : Option NodeId)
      (resident : d.nodes[parent]? = some n) (valid : bit ≤ 1) (shape : n.bit.size = 2) :
    SlotWrite d (.child parent bit) value (writeNode d parent { n with bit := n.bit.set! bit value })

theorem slotSet_returns_of_write {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) :
    Returns (liftAip (slotSet slot value)) (fun g => g.dev = some d)
      (fun _ g => g.dev = some final) := by
  intro g ambient device
  refine ⟨(), {g with dev := some final}, ambient, ?_, rfl⟩
  cases write with
  | root4 =>
    simp [liftAip, slotSet, getDev, modifyDev, device]
    rfl
  | root6 =>
    simp [liftAip, slotSet, getDev, modifyDev, device]
    rfl
  | child parent bit n _ resident valid shape =>
    simp [liftAip, slotSet, getNode, setNode, getDev, modifyDev, device,
      resident, Nat.not_lt.mpr valid, writeNode]
    rfl

/-- A branching node remains in the tree, but its owner is cleared. -/
theorem removeNodeSource_branching (d : Device) (id : NodeId) (n : AipNode)
    (left right : NodeId) (shape : n.bit = #[some left, some right]) :
    Returns (removeNodeSource id n) (fun g => g.dev = some d)
      (fun result g => result = .yield () ∧ g.dev = some (writeNode d id { n with peer := none })) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let after := mark (mark ambient .removeHasBit0 true) .removeHasBit1 true
  refine ⟨.yield (), {g with dev := some (writeNode d id {n with peer := none})},
    after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  simp [removeNodeSource, aipLift, liftAip, setNode, getDev, modifyDev,
    device, AipNode.bitAt, shape, branch, AmbientM.branch, writeNode, after, mark]
  rfl

theorem setNode_returns (d : Device) (id : NodeId) (n : AipNode) :
    Returns (liftAip (setNode id n)) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (writeNode d id n)) := by
  intro g ambient device
  refine ⟨(), {g with dev := some (writeNode d id n)}, ambient, ?_, rfl⟩
  simp [liftAip, setNode, getDev, modifyDev, device, writeNode]
  rfl

theorem reparent_returns (d : Device) (id : NodeId) (n : AipNode) (slot : Slot)
    (resident : d.nodes[id]? = some n) :
    Returns (do setNode id { (← getNode id) with parent := slot } : WG.M Unit)
      (fun g => g.dev = some d)
      (fun _ g => g.dev = some (writeNode d id { n with parent := slot })) := by
  intro g ambient device
  refine ⟨(), {g with dev := some (writeNode d id {n with parent := slot})}, ambient, ?_, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  simp [aipLift, liftAip, getNode, setNode, getDev, modifyDev, device, resident, writeNode]
  rfl

theorem freeNode_returns (d : Device) (id : NodeId) (n : AipNode)
    (resident : d.nodes[id]? = some n) :
    Returns (liftAip (freeNode id)) (fun g => g.dev = some d)
      (fun _ g => g.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient device
  refine ⟨(), {g with dev := some {d with nodes := d.nodes.erase id}}, ambient, ?_, rfl⟩
  simp [liftAip, freeNode, getNode, getDev, modifyDev, device, resident]
  rfl

def reparentNode (id : NodeId) (slot : Slot) : WG.M Unit := do
  setNode id { (← getNode id) with parent := slot }

def unaryBeforeChild (side : Bool) (id : NodeId) (n : AipNode) : WG.M Unit := do
  setNode id { n with peer := none }
  _ ← branch .removeHasBit0 side
  if side then
    _ ← branch .removeHasBit1 false
    pure ()
  _ ← branch .removeChildExists true
  pure ()

def unaryAfterLink (side : Bool) (id : NodeId) : WG.M (ForInStep Unit) := do
  _ ← branch .removeLeafBit0 (!side)
  if !side then
    _ ← branch .removeLeafBit1 false
    pure ()
  _ ← branch .removeFreeParent false
  freeNode id
  _ ← branch .removeNotFreeParent true
  pure (.yield ())

theorem unaryBeforeChild_returns (side : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    Returns (unaryBeforeChild side id n) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (writeNode d id { n with peer := none })) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let first := mark ambient .removeHasBit0 side
  let second := if side then mark first .removeHasBit1 false else first
  let after := mark second .removeChildExists true
  refine ⟨(), {g with dev := some (writeNode d id {n with peer := none})},
    after, ?_, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases side <;>
    simp [unaryBeforeChild, aipLift, liftAip, setNode, getDev, modifyDev,
      device, branch, AmbientM.branch, writeNode, after, second, first, mark]
  all_goals rfl

theorem unaryAfterLink_returns (side : Bool) (d : Device) (id : NodeId) (n : AipNode)
    (resident : d.nodes[id]? = some n) :
    Returns (unaryAfterLink side id) (fun g => g.dev = some d)
      (fun result g => result = .yield () ∧ g.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let first := mark ambient .removeLeafBit0 (!side)
  let second := if !side then mark first .removeLeafBit1 false else first
  let after := mark (mark second .removeFreeParent false) .removeNotFreeParent true
  refine ⟨.yield (), {g with dev := some {d with nodes := d.nodes.erase id}},
    after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases side <;>
    simp [unaryAfterLink, aipLift, liftAip, freeNode, getNode, getDev, modifyDev,
      device, resident, branch, AmbientM.branch, after, second, first, mark]
  all_goals rfl

theorem unary_source (side : Bool) (id : NodeId) (n : AipNode) (child : NodeId)
    (shape : n.bit = if side then #[some child, none] else #[none, some child]) :
    removeNodeSource id n = (do
      unaryBeforeChild side id n
      reparentNode child n.parent
      slotSet n.parent (some child)
      unaryAfterLink side id) := by
  funext g ambient
  cases side <;> simp [removeNodeSource, unaryBeforeChild, unaryAfterLink,
    reparentNode, AipNode.bitAt, shape, branch, AmbientM.branch, bind_assoc]

/-- Unary-node removal splices its child into any ready parent slot. The
read premises are over the successive Devices, so no aliasing is silently assumed away. -/
theorem removeNodeSource_unary (d : Device) (id : NodeId) (n : AipNode)
    (child : NodeId) (c : AipNode) (side : Bool)
    (shape : n.bit = if side then #[some child, none] else #[none, some child])
    (childRead : (writeNode d id { n with peer := none }).nodes[child]? = some c)
    (linked : Device) (write : SlotWrite
      (writeNode (writeNode d id { n with peer := none }) child { c with parent := n.parent })
      n.parent (some child) linked)
    (remaining : AipNode) (resident : linked.nodes[id]? = some remaining) :
    Returns (removeNodeSource id n) (fun g => g.dev = some d)
      (fun result g => result = .yield () ∧ g.dev = some { linked with nodes := linked.nodes.erase id }) := by
  rw [unary_source side id n child shape]
  refine returns_bind _ _ (unaryBeforeChild_returns side d id n) ?_
  intro u
  refine returns_bind _ _ (reparent_returns (writeNode d id { n with peer := none })
    child c n.parent childRead) ?_
  intro u
  refine returns_bind _ _ (slotSet_returns_of_write write) ?_
  intro u
  exact unaryAfterLink_returns side linked id remaining resident

end Leanux.Proofs.WG.Config
