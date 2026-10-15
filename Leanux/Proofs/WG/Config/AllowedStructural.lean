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
    Returns (slotSet slot value) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some final) := by
  cases write <;> rw [returns_iff]
  all_goals mvcgen [slotSet, getNode, getDev, getK, setNode, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]
  all_goals omega

/-- A branching node remains in the tree, but its owner is cleared. -/
theorem removeNodeSource_branching (d : Device) (id : NodeId) (n : AipNode)
    (left right : NodeId) (shape : n.bit = #[some left, some right]) :
    Returns (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some (writeNode d id { n with peer := none })) := by
  rw [returns_iff]
  simp [removeNodeSource, AipNode.bitAt, shape, branch, bind_assoc]
  mvcgen [setNode, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]

theorem setNode_returns (d : Device) (id : NodeId) (n : AipNode) :
    Returns (setNode id n) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (writeNode d id n)) := by
  rw [returns_iff]
  mvcgen [setNode, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]

theorem reparent_returns (d : Device) (id : NodeId) (n : AipNode) (slot : Slot)
    (resident : d.nodes[id]? = some n) :
    Returns (do setNode id { (← getNode id) with parent := slot })
      (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (writeNode d id { n with parent := slot })) := by
  rw [returns_iff]
  mvcgen [getNode, getDev, getK, setNode, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]

theorem freeNode_returns (d : Device) (id : NodeId) (n : AipNode)
    (resident : d.nodes[id]? = some n) :
    Returns (freeNode id) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with nodes := d.nodes.erase id }) := by
  rw [returns_iff]
  mvcgen [freeNode, getNode, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

def reparentNode (id : NodeId) (slot : Slot) : M Unit := do
  setNode id { (← getNode id) with parent := slot }

def unaryBeforeChild (side : Bool) (id : NodeId) (n : AipNode) : M Unit := do
  setNode id { n with peer := none }
  _ ← branch .removeHasBit0 side
  if side then
    _ ← branch .removeHasBit1 false
    pure ()
  _ ← branch .removeChildExists true
  pure ()

def unaryAfterLink (side : Bool) (id : NodeId) : M (ForInStep Unit) := do
  _ ← branch .removeLeafBit0 (!side)
  if !side then
    _ ← branch .removeLeafBit1 false
    pure ()
  _ ← branch .removeFreeParent false
  freeNode id
  _ ← branch .removeNotFreeParent true
  pure (.yield ())

theorem unaryBeforeChild_returns (side : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    Returns (unaryBeforeChild side id n) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (writeNode d id { n with peer := none })) := by
  rw [returns_iff]
  mvcgen [unaryBeforeChild, branch, setNode, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [writeNode]

theorem unaryAfterLink_returns (side : Bool) (d : Device) (id : NodeId) (n : AipNode)
    (resident : d.nodes[id]? = some n) :
    Returns (unaryAfterLink side id) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some { d with nodes := d.nodes.erase id }) := by
  rw [returns_iff]
  mvcgen [unaryAfterLink, branch, freeNode, getNode, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem unary_source (side : Bool) (id : NodeId) (n : AipNode) (child : NodeId)
    (shape : n.bit = if side then #[some child, none] else #[none, some child]) :
    removeNodeSource id n = (do
      unaryBeforeChild side id n
      reparentNode child n.parent
      slotSet n.parent (some child)
      unaryAfterLink side id) := by
  cases side <;> simp [removeNodeSource, unaryBeforeChild, unaryAfterLink,
    reparentNode, AipNode.bitAt, shape, branch, bind_assoc, Functor.discard, Functor.mapConst]

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
    Returns (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some { linked with nodes := linked.nodes.erase id }) := by
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
