import AllowedipsTrieNodeWalk

namespace Binary.Pair.Trie
open Leanux Leanux.WG

def changeChild (parentId direction fresh : Nat) (entry : NodeId×Node) : NodeId×Node :=
  (entry.1,if entry.1=parentId then {entry.2 with children:=entry.2.children.set! direction (some fresh)} else entry.2)

theorem changeChild_key (parentId direction fresh : Nat) (entry : NodeId×Node) :
    (changeChild parentId direction fresh entry).1=entry.1 := rfl

theorem find_changeChild (nodes : List (NodeId×Node)) (parentId direction fresh id : Nat) :
    (nodes.map (changeChild parentId direction fresh)).find? (·.1==id)=
      (nodes.find? (·.1==id)).map (changeChild parentId direction fresh) := by
  induction nodes with
  | nil => rfl
  | cons entry nodes ih =>
    simp only [List.map_cons,List.find?_cons,changeChild_key]
    split <;> simp_all

theorem nodeChildren_set_empty {id direction fresh : Nat} {node : Node} {left right : Option Nat}
    (shape : node.children=#[left,right]) (bit : direction<2)
    (empty : node.children[direction]?=some none) :
    (nodeChildren (id,{node with children:=node.children.set! direction (some fresh)})).Perm
      (fresh::nodeChildren (id,node)) := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl
  · rw [shape] at empty
    have leftNone : left=none := Option.some.inj empty
    subst left
    cases right <;> simp [nodeChildren,edgeChildren,shape]
  · rw [shape] at empty
    have rightNone : right=none := Option.some.inj empty
    subst right
    cases left with
    | none => simp [nodeChildren,edgeChildren,shape]
    | some child =>
      simpa [nodeChildren,edgeChildren,shape] using List.Perm.swap fresh child []

/-- Replacing the unique empty parent slot adds exactly one occurrence of the
fresh identity to the executable heap walk's collected children. -/
theorem children_changeChild_perm {nodes : List (NodeId×Node)} {parentId direction fresh : Nat}
    {parentNode : Node} {left right : Option Nat}
    (unique : (nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (empty : parentNode.children[direction]?=some none) :
    ((nodes.map (changeChild parentId direction fresh)).flatMap nodeChildren).Perm
      (fresh::nodes.flatMap nodeChildren) := by
  induction nodes with
  | nil => cases parent
  | cons entry nodes ih =>
    have unique := List.nodup_cons.mp unique
    rcases List.mem_cons.mp parent with equal | member
    · subst entry
      have later : nodes.map (changeChild parentId direction fresh)=nodes := by
        apply (List.map_congr_left (g:=id) ?_).trans (List.map_id nodes)
        intro entry present
        have different : entry.1≠parentId := by
          intro same
          exact unique.1 (same ▸ List.mem_map.mpr ⟨entry,present,rfl⟩)
        simp only [changeChild,ite_eq_right different]
        rfl
      simp only [List.map_cons,later,List.flatMap_cons,changeChild,ite_true]
      exact List.Perm.append_right (nodes.flatMap nodeChildren) (nodeChildren_set_empty shape bit empty)
    · have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨(parentId,parentNode),member,rfl⟩)
      simp only [List.map_cons,List.flatMap_cons,changeChild,ite_eq_right different]
      have step := ih unique.2 member
      exact (List.Perm.append_left (nodeChildren entry) step).trans List.perm_middle

#print axioms children_changeChild_perm
end Binary.Pair.Trie
