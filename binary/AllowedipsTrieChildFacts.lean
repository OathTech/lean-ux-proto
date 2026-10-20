import AllowedipsTrieChildList

namespace Binary.Pair.Trie
open Leanux Leanux.WG

def attachedChild (s : State) (parentId direction fresh : Nat) (leaf : Node) : State :=
  {s with nodes:=s.nodes.map (changeChild parentId direction fresh)++[(fresh,leaf)]}

theorem find_node_key {α : Type} {nodes : List (NodeId×α)} {id : Nat} {node : α}
    (unique : (nodes.map Prod.fst).Nodup) (member : (id,node) ∈ nodes) :
    nodes.find? (·.1==id)=some (id,node) := by
  induction nodes with
  | nil => cases member
  | cons entry nodes ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : entry.1≠id := by
        intro same
        exact parts.1 (same ▸ List.mem_map.mpr ⟨(id,node),member,rfl⟩)
      simpa only [List.find?_cons,show (entry.1==id)=false from by simp [different]] using ih parts.2 member

theorem find_attached_old {s : State} {id : Nat} {node : Node}
    (found : s.nodes.find? (·.1==id)=some (id,node)) (parentId direction fresh : Nat) (leaf : Node) :
    (attachedChild s parentId direction fresh leaf).nodes.find? (·.1==id)=
      some (changeChild parentId direction fresh (id,node)) := by
  simp only [attachedChild,List.find?_append,find_changeChild,found,Option.map_some,Option.some_or]

theorem find_attached_fresh {s : State} {fresh : Nat}
    (absent : ∀ entry ∈ s.nodes, entry.1≠fresh) (parentId direction : Nat) (leaf : Node) :
    (attachedChild s parentId direction fresh leaf).nodes.find? (·.1==fresh)=some (fresh,leaf) := by
  have missing : s.nodes.find? (·.1==fresh)=none :=
    List.find?_eq_none.mpr (fun entry member => by simpa using absent entry member)
  simp only [attachedChild,List.find?_append,find_changeChild,missing,Option.map_none]
  simp

/-- Child-field changes preserve every old edge's arithmetic facts. The node
lookup itself is updated, so this does not assume its old bytes stayed equal. -/
theorem edgeFacts_attached_old {s : State} {roots : List (Option Nat)} {node : Node} {edge}
    (facts : EdgeFacts s roots node edge) (parentId direction fresh : Nat) (leaf : Node) :
    EdgeFacts (attachedChild s parentId direction fresh leaf) roots node edge := by
  intro next equal
  obtain ⟨child,found,notRoot,width,measure,prefixEq,side⟩ := facts next equal
  refine ⟨(changeChild parentId direction fresh (next,child)).2,
    find_attached_old found parentId direction fresh leaf,notRoot,?_,?_,?_,?_⟩ <;>
    simp only [changeChild] <;> split <;> assumption

theorem edgeFacts_children {s : State} {roots} {node : Node} {children : Array (Option NodeId)} {edge} :
    EdgeFacts s roots {node with children} edge=EdgeFacts s roots node edge := rfl

theorem edgeFacts_set_empty {s : State} {roots} {node : Node} {left right : Option Nat}
    {direction fresh : Nat} (shape : node.children=#[left,right]) (bit : direction<2)
    (empty : node.children[direction]?=some none)
    (old : ∀ edge ∈ node.children.toList.zipIdx, EdgeFacts s roots node edge)
    (new : EdgeFacts s roots node (some fresh,direction)) :
    ∀ edge ∈ (node.children.set! direction (some fresh)).toList.zipIdx,
      EdgeFacts s roots {node with children:=node.children.set! direction (some fresh)} edge := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl <;> intro edge member
  · rw [shape] at empty
    have leftNone : left=none := Option.some.inj empty
    subst left
    simp only [shape] at member
    have cases : edge=(some fresh,0) ∨ edge=(right,1) := by simpa using member
    rcases cases with rfl|rfl
    · exact new
    · exact old (right,1) (by simp [shape])
  · rw [shape] at empty
    have rightNone : right=none := Option.some.inj empty
    subst right
    simp only [shape] at member
    have cases : edge=(left,0) ∨ edge=(some fresh,1) := by simpa using member
    rcases cases with rfl|rfl
    · exact old (left,0) (by simp [shape])
    · exact new

#print axioms edgeFacts_attached_old
#print axioms edgeFacts_set_empty
end Binary.Pair.Trie
