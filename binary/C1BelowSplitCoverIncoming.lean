import C1BelowSplitCoverSource
import C1BelowSplitCoverTrieHeap
import AllowedipsChildHeap

/- Origin: trial source binary-trials/t2/CoverIncoming.lean (copied in t5) on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T2, part 3b: incoming-edge walks of the structural check after the
covering insertion. -/
namespace Binary.Pair.Trie.C1Split
open Leanux Leanux.WG

/-- A child held in one slot is held nowhere else: by no other node, and not by
the same node's other slot. -/
theorem heap_occupant_unique {s : State} {roots : List (Option NodeId)}
    {parentId direction down : Nat} {parentNode : Node} {left right : Option Nat}
    (checked : heap s roots=.ok ()) (parent : (parentId,parentNode) ∈ s.nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (occupied : parentNode.children[direction]?=some (some down)) :
    (∀ entry ∈ s.nodes, entry≠(parentId,parentNode) → some down ∉ entry.2.children.toList) ∧
    (direction=0 → right≠some down) ∧ (direction=1 → left≠some down) := by
  have parts := List.pairwise_flatMap.mp (heap_children_nodup checked)
  have which : direction=0 ∨ direction=1 := by omega
  have held : down ∈ nodeChildren (parentId,parentNode) := by
    rcases which with rfl|rfl <;> rw [shape] at occupied
    · have leftSome : left=some down := Option.some.inj occupied
      subst left
      simp [nodeChildren,edgeChildren,shape]
    · have rightSome : right=some down := Option.some.inj occupied
      subst right
      simp [nodeChildren,edgeChildren,shape]
  have own := parts.1 _ parent
  refine ⟨?_,?_,?_⟩
  · intro entry member different child
    obtain ⟨index,atIndex⟩ := List.mem_iff_getElem?.mp child
    have collected : down ∈ nodeChildren entry :=
      List.mem_flatMap.mpr ⟨(some down,index),List.mk_mem_zipIdx_iff_getElem?.mpr atIndex,by simp [edgeChildren]⟩
    exact pairwise_mem_ne (R:=fun a b : NodeId×Node => ∀ x ∈ nodeChildren a, ∀ y ∈ nodeChildren b, x≠y)
      (fun a b h x hx y hy equal => h y hy x hx equal.symm) parts.2 member parent different
      down collected down held rfl
  · rintro rfl equal
    rw [shape] at occupied
    have leftSome : left=some down := Option.some.inj occupied
    subst left
    subst right
    simp [nodeChildren,edgeChildren,shape] at own
  · rintro rfl equal
    rw [shape] at occupied
    have rightSome : right=some down := Option.some.inj occupied
    subst right
    subst left
    simp [nodeChildren,edgeChildren,shape] at own

#print axioms heap_occupant_unique
end Binary.Pair.Trie.C1Split

namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

theorem coverUpdate_bit (downId b parentId direction fresh : Nat) (entry : NodeId×AipNode) :
    (coverUpdate downId b parentId direction fresh entry).2.bit=
      (installChild parentId direction fresh entry).2.bit := by
  rcases entry with ⟨current,node⟩
  by_cases p : current=parentId
  · subst p
    by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild]
    · simp [coverUpdate,reparent,installChild,q]
  · by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild,p]
    · simp [coverUpdate,reparent,installChild,p,q]

theorem incomingStep_cover (id downId b parentId direction fresh : Nat) (entry : NodeId×AipNode)
    (before : List Slot) :
    incomingStep id (coverUpdate downId b parentId direction fresh entry) before=
      incomingStep id (installChild parentId direction fresh entry) before := by
  unfold incomingStep
  rw [coverUpdate_bit]
  rfl

theorem incomingStep_replace_old {id parentId direction fresh downId : Nat} {node : AipNode}
    {left right : Option Nat} (shape : node.bit=#[left,right]) (bit : direction<2)
    (occupied : node.bit[direction]?=some (some downId)) (different : id≠fresh) (notDown : id≠downId)
    (before : List Slot) :
    incomingStep id (installChild parentId direction fresh (parentId,node)) before=
      incomingStep id (parentId,node) before := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl <;> rw [shape] at occupied
  · have leftSome : left=some downId := Option.some.inj occupied
    subst left
    simp [incomingStep,installChild,shape,Ne.symm different,Ne.symm notDown]
  · have rightSome : right=some downId := Option.some.inj occupied
    subst right
    simp [incomingStep,installChild,shape,Ne.symm different,Ne.symm notDown]

theorem incomingStep_replace_new {parentId direction fresh : Nat} {node : AipNode}
    {left right : Option Nat} (shape : node.bit=#[left,right]) (bit : direction<2)
    (absent : some fresh ∉ node.bit.toList) (before : List Slot) :
    incomingStep fresh (installChild parentId direction fresh (parentId,node)) before=
      .ok (.yield (.child parentId direction::before)) := by
  have which : direction=0 ∨ direction=1 := by omega
  have leftNe : left≠some fresh := by simpa [shape] using (fun same => absent (by simp [shape,same]))
  have rightNe : right≠some fresh := by simpa [shape] using (fun same => absent (by simp [shape,same]))
  rcases which with rfl|rfl
  · simp [incomingStep,installChild,shape,rightNe]
    rfl
  · simp [incomingStep,installChild,shape,leftNe]
    rfl

theorem incoming_cover_walk {nodes : List (NodeId×AipNode)} {downId b parentId direction fresh : Nat}
    {parentNode : AipNode} {left right : Option Nat}
    (unique : (nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2)
    (absent : ∀ entry ∈ nodes, some fresh ∉ entry.2.bit.toList) (before : List Slot) :
    forIn (nodes.map (coverUpdate downId b parentId direction fresh)) before (incomingStep fresh)=
      .ok (.child parentId direction::before) := by
  induction nodes generalizing before with
  | nil => cases parent
  | cons entry nodes ih =>
    have unique := List.nodup_cons.mp unique
    rcases List.mem_cons.mp parent with equal | member
    · subst entry
      rw [List.map_cons,List.forIn_cons,incomingStep_cover,
        incomingStep_replace_new shape bit (absent (parentId,parentNode) (by simp))]
      dsimp only [Bind.bind,Except.bind]
      apply forIn_identity
      intro pair present current
      obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp present
      have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨entry,atEntry,rfl⟩)
      rw [incomingStep_cover]
      simp only [installChild,ite_eq_right different]
      exact incomingStep_absent fresh entry (absent entry (by simp [atEntry])) current
    · have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨(parentId,parentNode),member,rfl⟩)
      rw [List.map_cons,List.forIn_cons]
      have first : incomingStep fresh (coverUpdate downId b parentId direction fresh entry) before=
          .ok (.yield before) := by
        rw [incomingStep_cover]
        simp only [installChild,ite_eq_right different]
        exact incomingStep_absent fresh entry (absent entry (by simp)) before
      rw [first]
      exact ih unique.2 member (fun e h => absent e (List.mem_cons_of_mem entry h)) before

#print axioms incoming_cover_walk

/-- One incoming child edge and no root edge satisfy the structural check. -/
theorem structureCheck_single {s : State} {id owner side : Nat} {node : AipNode}
    (other4 : s.table.root4≠some id) (other6 : s.table.root6≠some id)
    (walk : forIn s.nodes [] (incomingStep id)=.ok [Slot.child owner side])
    (parentEq : node.parent=.child owner side) :
    structureCheck s id node=.ok () := by
  rw [structureCheck_walk]
  simp only [rootStep,other4,other6,beq_iff_eq,ite_false,List.forIn_cons,List.forIn_nil]
  change (do
    let incoming ← forIn s.nodes [] (incomingStep id)
    unless incoming==[node.parent] do throw s!"heap.parent[{id}]: {repr incoming}")=.ok ()
  rw [walk,parentEq]
  have self : ([Slot.child owner side]==[Slot.child owner side])=true := by
    change ((owner==owner && side==side) && true)=true
    simp
  dsimp only [Bind.bind,Except.bind]
  rw [self]
  rfl

#print axioms structureCheck_single
end Binary.Pair.Allowedips.C1Split
