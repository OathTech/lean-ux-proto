import Leanux.Proofs.WG.Config.AllowedPairsFrames

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem nodePairs_write (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit.size = 2) : NodePairs (writeNode d id n) := by
  intro other p resident
  by_cases same : id = other
  · subst other
    have sameNode : n = p := by simpa [writeNode] using resident
    simpa [← sameNode] using shape
  · have old : d.nodes[other]? = some p := by
      simpa [writeNode, Std.TreeMap.getElem?_insert, same] using resident
    exact pairs other p old

theorem nodePairs_erase (d : Device) (id : NodeId) (pairs : NodePairs d) :
    NodePairs { d with nodes := d.nodes.erase id } := by
  intro other p resident
  by_cases same : id = other
  · subst other
    simp at resident
  · apply pairs other p
    simpa [Std.TreeMap.getElem?_erase, same] using resident

theorem slotWrite_nodePairs {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) (pairs : NodePairs d) : NodePairs final := by
  cases write with
  | root4 => exact pairs
  | root6 => exact pairs
  | child parent bit n value resident valid shape =>
    exact nodePairs_write d parent _ pairs (by simpa using shape)

theorem childReparent_nodePairs {d final : Device} {child : Option NodeId} {slot : Slot}
    (write : ChildReparent d child slot final) (pairs : NodePairs d) : NodePairs final := by
  cases write with
  | none => exact pairs
  | some id n slot resident => exact nodePairs_write d id _ pairs (pairs id n resident)

theorem nodeRemoval_nodePairs {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) (pairs : NodePairs d) : NodePairs final := by
  cases step with
  | branching left right shape => exact nodePairs_write d id _ pairs (by simp [shape])
  | unary child c side shape read linked write remaining resident =>
    have cleared := nodePairs_write d id { n with peer := none } pairs (by cases side <;> simp [shape])
    have reparent := nodePairs_write _ child { c with parent := n.parent } cleared (cleared child c read)
    exact nodePairs_erase _ id (slotWrite_nodePairs write reparent)
  | leaf linked shape write choice remaining resident =>
    exact nodePairs_erase _ id (slotWrite_nodePairs write
      (nodePairs_write d id _ pairs (by simp [shape])))
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write resident =>
    have cleared := nodePairs_write d id { n with peer := none } pairs (by simp [shape])
    have removed := nodePairs_erase detached id (slotWrite_nodePairs unlink cleared)
    exact nodePairs_erase _ parent (slotWrite_nodePairs write (childReparent_nodePairs reparent removed))

theorem removalRun_nodePairs {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) (pairs : NodePairs d) : NodePairs final := by
  induction steps with
  | nil => exact pairs
  | cons d id rest n next final read step tail ih =>
    exact ih (nodeRemoval_nodePairs step (deleteListedNodes_nodePairs id d pairs))

theorem removalEffect_nodePairs {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (pairs : NodePairs d) : NodePairs final := by
  cases ids with
  | nil => subst final; exact pairs
  | cons id rest => exact removalRun_nodePairs steps pairs

end Leanux.Proofs.WG.Config
