import AllowedipsChildOwnership
import AllowedipsTrieChildHeap

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem incomingStep_child_old {id parentId direction fresh : Nat} {node : AipNode}
    {left right : Option Nat} (shape : node.bit=#[left,right]) (bit : direction<2)
    (empty : node.bit[direction]?=some none) (different : id≠fresh) (before : List Slot) :
    incomingStep id (installChild parentId direction fresh (parentId,node)) before=
      incomingStep id (parentId,node) before := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl <;> rw [shape] at empty
  · have leftNone : left=none := Option.some.inj empty
    subst left
    simp [incomingStep,installChild,shape,Ne.symm different]
  · have rightNone : right=none := Option.some.inj empty
    subst right
    simp [incomingStep,installChild,shape,Ne.symm different]

theorem incomingStep_child_new {parentId direction fresh : Nat} {node : AipNode}
    {left right : Option Nat} (shape : node.bit=#[left,right]) (bit : direction<2)
    (empty : node.bit[direction]?=some none) (absent : some fresh ∉ node.bit.toList) (before : List Slot) :
    incomingStep fresh (installChild parentId direction fresh (parentId,node)) before=
      .ok (.yield (.child parentId direction::before)) := by
  have which : direction=0 ∨ direction=1 := by omega
  have leftNe : left≠some fresh := by simpa [shape] using (fun same => absent (by simp [shape,same]))
  have rightNe : right≠some fresh := by simpa [shape] using (fun same => absent (by simp [shape,same]))
  rcases which with rfl|rfl <;> rw [shape] at empty
  · have leftNone : left=none := Option.some.inj empty
    subst left
    simp [incomingStep,installChild,shape,rightNe]
    rfl
  · have rightNone : right=none := Option.some.inj empty
    subst right
    simp [incomingStep,installChild,shape,leftNe]
    rfl

theorem incoming_child_walk {nodes : List (NodeId×AipNode)} {parentId direction fresh : Nat}
    {parentNode : AipNode} {left right : Option Nat}
    (unique : (nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2)
    (empty : parentNode.bit[direction]?=some none)
    (absent : ∀ entry ∈ nodes, some fresh ∉ entry.2.bit.toList) (before : List Slot) :
    forIn (nodes.map (installChild parentId direction fresh)) before (incomingStep fresh)=
      .ok (.child parentId direction::before) := by
  induction nodes generalizing before with
  | nil => cases parent
  | cons entry nodes ih =>
    have unique := List.nodup_cons.mp unique
    rcases List.mem_cons.mp parent with equal | member
    · subst entry
      rw [List.map_cons,List.forIn_cons,incomingStep_child_new shape bit empty (absent (parentId,parentNode) (by simp))]
      dsimp only [Bind.bind,Except.bind]
      apply forIn_identity
      intro pair present current
      obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp present
      have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨entry,atEntry,rfl⟩)
      simp only [installChild,ite_eq_right different]
      exact incomingStep_absent fresh entry (absent entry (by simp [atEntry])) current
    · have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨(parentId,parentNode),member,rfl⟩)
      rw [List.map_cons,List.forIn_cons]
      have first : incomingStep fresh (installChild parentId direction fresh entry) before=.ok (.yield before) := by
        simp only [installChild,ite_eq_right different]
        exact incomingStep_absent fresh entry (absent entry (by simp)) before
      rw [first]
      exact ih unique.2 member (fun e h => absent e (List.mem_cons_of_mem entry h)) before

#print axioms incoming_child_walk
end Binary.Pair.Allowedips
