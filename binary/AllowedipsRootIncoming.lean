import AllowedipsRootTree

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Binary.Pair.Allowedips.Model

def rootStep (id : NodeId) (node : AipNode) (entry : Option NodeId×Slot×Nat)
    (incoming : List Slot) : Except String (ForInStep (List Slot)) := do
  if entry.1==some id then
    unless node.bitlen==entry.2.2 do throw "heap.root-family"
    return .yield (entry.2.1::incoming)
  else return .yield incoming

def incomingStep (id : NodeId) (entry : NodeId×AipNode)
    (incoming : List Slot) : Except String (ForInStep (List Slot)) := do
  let result ← forIn entry.2.bit.toList.zipIdx incoming fun (child,bit) before =>
    pure (.yield (if child==some id then .child entry.1 bit::before else before))
  return .yield result

theorem structureCheck_walk (s : State) (id : NodeId) (node : AipNode) :
    structureCheck s id node=(do
      let incoming ← forIn [(s.table.root4,Slot.root4,32),(s.table.root6,Slot.root6,128)] [] (rootStep id node)
      let incoming ← forIn s.nodes incoming (incomingStep id)
      unless incoming==[node.parent] do throw s!"heap.parent[{id}]: {repr incoming}") := by
  simp only [structureCheck]
  congr 1
  funext incoming
  congr 1
  apply forIn_congr_mem
  intro pair _ before
  unfold incomingStep
  congr 1
  apply forIn_congr_mem
  intro edge _ prior
  dsimp only
  split <;> rfl

theorem incomingStep_leaf (id fresh key cidr width pid : Nat) (parent : Slot) (incoming : List Slot) :
    incomingStep id (fresh,{newNode key cidr width (some pid) with parent}) incoming=.ok (.yield incoming) := rfl

theorem structureCheck_installed_old (s : State) (v4 : Bool) (key cidr pid id : Nat) (node : AipNode)
    (empty : (if v4 then s.table.root4 else s.table.root6)=none)
    (different : id≠s.nextNode) :
    structureCheck (installedRoot v4 key cidr pid s) id node=structureCheck s id node := by
  have roots : forIn [((installedRoot v4 key cidr pid s).table.root4,Slot.root4,32),
      ((installedRoot v4 key cidr pid s).table.root6,Slot.root6,128)] [] (rootStep id node)=
      forIn [(s.table.root4,Slot.root4,32),(s.table.root6,Slot.root6,128)] [] (rootStep id node) := by
    cases v4 <;> simp_all [installedRoot,List.forIn_cons,List.forIn_nil,rootStep,Ne.symm different]
  rw [structureCheck_walk,structureCheck_walk,roots]
  congr 1
  funext incoming
  have unchanged : forIn (installedRoot v4 key cidr pid s).nodes incoming (incomingStep id)=
      forIn s.nodes incoming (incomingStep id) := by
    apply forIn_append_identity
    intro pair member before
    obtain rfl : pair=(s.nextNode,{newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4}) :=
      List.mem_singleton.mp member
    exact incomingStep_leaf _ _ _ _ _ _ _ _
  rw [unchanged]

theorem incomingStep_absent (id : NodeId) (entry : NodeId×AipNode)
    (absent : some id ∉ entry.2.bit.toList) (incoming : List Slot) :
    incomingStep id entry incoming=.ok (.yield incoming) := by
  unfold incomingStep
  have same : forIn entry.2.bit.toList.zipIdx incoming
      (fun (child,bit) before =>
        (pure (.yield (if child==some id then Slot.child entry.1 bit::before else before)) :
          Except String (ForInStep (List Slot))))=.ok incoming := by
    apply forIn_identity
    intro pair member before
    have atChild := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member)
    have different : pair.1≠some id := by intro equal; exact absent (equal ▸ atChild)
    simp [different]
    rfl
  rw [same]
  rfl

namespace Root

theorem structureCheck_installed_new {s : State} {names m} (v4 : Bool) (key cidr pid : Nat)
    (shape : heap names s m=.ok ()) (below : ∀ pair ∈ s.nodes, pair.1<s.nextNode)
    (empty : (if v4 then s.table.root4 else s.table.root6)=none) :
    structureCheck (installedRoot v4 key cidr pid s) s.nextNode
      {newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4}=.ok () := by
  have other4 : s.table.root4≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below shape below s.nextNode (by simp [equal])
    omega
  have other6 : s.table.root6≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below shape below s.nextNode (by simp [equal])
    omega
  have children (incoming : List Slot) : forIn (installedRoot v4 key cidr pid s).nodes incoming
      (incomingStep s.nextNode)=.ok incoming := by
    apply forIn_identity
    intro pair member before
    rcases List.mem_append.mp member with old | new
    · apply incomingStep_absent
      intro child
      have bound : s.nextNode<s.nextNode := edges_below shape below pair.1 pair.2 old s.nextNode child
      omega
    · obtain rfl := List.mem_singleton.mp new
      exact incomingStep_leaf _ _ _ _ _ _ _ _
  rw [structureCheck_walk]
  cases v4 <;> simp_all [installedRoot,List.forIn_cons,List.forIn_nil,rootStep,newNode,rootWidth,rootSlot] <;> rfl

end Root
#print axioms structureCheck_installed_old
#print axioms Root.structureCheck_installed_new
end Binary.Pair.Allowedips
