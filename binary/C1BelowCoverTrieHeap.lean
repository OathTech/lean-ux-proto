import AllowedipsTrieChildHeap

/-! Origin: trial T2, `binary-trials/t2/CoverTrieHeap.lean` on `task/binary-trials` (unreviewed), copied
under the package prefix with the namespaces suffixed `C1Cover`; proofs unchanged. -/

/-! Trial T2, part 3a: the trie-level graph assertion after splicing a fresh node
between a parent and its occupied child slot. -/
namespace Binary.Pair.Trie.C1Cover
open Leanux Leanux.WG

/-- `edgeFacts_set_empty` without the emptiness premise: whatever the slot held. -/
theorem edgeFacts_set_slot {s : State} {roots} {node : Node} {left right : Option Nat}
    {direction fresh : Nat} (shape : node.children=#[left,right]) (bit : direction<2)
    (old : ∀ edge ∈ node.children.toList.zipIdx, EdgeFacts s roots node edge)
    (new : EdgeFacts s roots node (some fresh,direction)) :
    ∀ edge ∈ (node.children.set! direction (some fresh)).toList.zipIdx,
      EdgeFacts s roots {node with children:=node.children.set! direction (some fresh)} edge := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl <;> intro edge member
  · simp only [shape] at member
    have cases : edge=(some fresh,0) ∨ edge=(right,1) := by simpa using member
    rcases cases with rfl|rfl
    · exact new
    · exact old (right,1) (by simp [shape])
  · simp only [shape] at member
    have cases : edge=(left,0) ∨ edge=(some fresh,1) := by simpa using member
    rcases cases with rfl|rfl
    · exact old (left,0) (by simp [shape])
    · exact new

/-- Replacing an occupied slot moves its old occupant out of the collected children. -/
theorem nodeChildren_set_occupied {id direction fresh down : Nat} {node : Node} {left right : Option Nat}
    (shape : node.children=#[left,right]) (bit : direction<2)
    (occupied : node.children[direction]?=some (some down)) :
    (nodeChildren (id,{node with children:=node.children.set! direction (some fresh)})++[down]).Perm
      (fresh::nodeChildren (id,node)) := by
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl
  · rw [shape] at occupied
    have leftSome : left=some down := Option.some.inj occupied
    subst left
    cases right with
    | none => simp [nodeChildren,edgeChildren,shape]
    | some child =>
      simpa [nodeChildren,edgeChildren,shape] using
        (List.Perm.cons fresh (List.Perm.swap down child [])).trans (List.Perm.refl _)
  · rw [shape] at occupied
    have rightSome : right=some down := Option.some.inj occupied
    subst right
    cases left with
    | none => simp [nodeChildren,edgeChildren,shape]
    | some child =>
      simpa [nodeChildren,edgeChildren,shape] using
        (List.Perm.swap fresh child [down])

theorem children_replaceChild_perm {nodes : List (NodeId×Node)} {parentId direction fresh down : Nat}
    {parentNode : Node} {left right : Option Nat}
    (unique : (nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (occupied : parentNode.children[direction]?=some (some down)) :
    ((nodes.map (changeChild parentId direction fresh)).flatMap nodeChildren++[down]).Perm
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
      have node := nodeChildren_set_occupied (id:=parentId) (fresh:=fresh) shape bit occupied
      rw [List.append_assoc]
      refine (List.Perm.append_left _ List.perm_append_comm).trans ?_
      rw [←List.append_assoc]
      exact List.Perm.append_right (nodes.flatMap nodeChildren) node
    · have different : entry.1≠parentId := by
        intro same
        exact unique.1 (same ▸ List.mem_map.mpr ⟨(parentId,parentNode),member,rfl⟩)
      simp only [List.map_cons,List.flatMap_cons,changeChild,ite_eq_right different]
      have step := ih unique.2 member
      rw [List.append_assoc]
      exact (List.Perm.append_left (nodeChildren entry) step).trans List.perm_middle

/-- Splicing a fresh node between `parent` and the child `down` in its slot
preserves the executable graph assertion. -/
theorem heap_spliced_child {s : State} {roots : List (Option NodeId)}
    {parentId direction fresh downId b : Nat} {parentNode downNode leaf : Node} {left right : Option Nat}
    (checked : heap s roots=.ok ()) (unique : (s.nodes.map Prod.fst).Nodup)
    (absent : ∀ entry ∈ s.nodes, entry.1≠fresh) (parent : (parentId,parentNode) ∈ s.nodes)
    (down : (downId,downNode) ∈ s.nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (occupied : parentNode.children[direction]?=some (some downId))
    (downBit : b<2) (leafChildren : leaf.children=(#[none,none] : Array (Option NodeId)).set! b (some downId))
    (width : leaf.width=parentNode.width) (measure : parentNode.cidr<leaf.cidr)
    (prefixEq : leaf.key/2^(parentNode.width-parentNode.cidr)=parentNode.key/2^(parentNode.width-parentNode.cidr))
    (side : leaf.key/2^(parentNode.width-1-parentNode.cidr)%2=direction)
    (downMeasure : leaf.cidr<downNode.cidr)
    (downPrefix : downNode.key/2^(leaf.width-leaf.cidr)=leaf.key/2^(leaf.width-leaf.cidr))
    (downSide : downNode.key/2^(leaf.width-1-leaf.cidr)%2=b) :
    heap (attachedChild s parentId direction fresh leaf) roots=.ok () := by
  have notRoot : some fresh ∉ roots := by
    intro root
    obtain ⟨node,member⟩ := heap_root checked root
    exact absent (fresh,node) member rfl
  have downEdge : (some downId,direction) ∈ parentNode.children.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa using occupied
  obtain ⟨child,found,downNotRoot,downWidth,_⟩ :=
    heap_edge_facts checked parentId parentNode parent _ downEdge downId rfl
  have childEq : child=downNode := congrArg Prod.snd
    (Option.some.inj (found.symm.trans (find_node_key unique down)))
  subst child
  have newEdge : EdgeFacts (attachedChild s parentId direction fresh leaf) roots parentNode (some fresh,direction) := by
    intro next equal
    cases Option.some.inj equal
    exact ⟨leaf,find_attached_fresh absent parentId direction leaf,notRoot,width,measure,prefixEq,side⟩
  have leafEdge : EdgeFacts (attachedChild s parentId direction fresh leaf) roots leaf (some downId,b) := by
    intro next equal
    cases Option.some.inj equal
    refine ⟨(changeChild parentId direction fresh (downId,downNode)).2,
      find_attached_old found parentId direction fresh leaf,downNotRoot,?_,?_,?_,?_⟩ <;>
      simp only [changeChild] <;> split <;> first | assumption | exact downWidth.trans width.symm
  apply heap_of_facts
  · intro id root
    obtain ⟨node,member⟩ := heap_root checked root
    exact ⟨(changeChild parentId direction fresh (id,node)).2,
      List.mem_append_left _ (List.mem_map.mpr ⟨(id,node),member,rfl⟩)⟩
  · intro id node member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
      cases equal
      have oldEdges := fun edge atEdge => edgeFacts_attached_old
        (heap_edge_facts checked current original present edge atEdge) parentId direction fresh leaf
      by_cases same : current=parentId
      · subst current
        have parentEq : original=parentNode := congrArg Prod.snd
          (Option.some.inj ((find_node_key unique present).symm.trans (find_node_key unique parent)))
        subst original
        simpa only [changeChild,ite_true] using edgeFacts_set_slot shape bit oldEdges newEdge
      · simpa only [changeChild,ite_eq_right same] using oldEdges
    · obtain equal := List.mem_singleton.mp new
      cases equal
      intro edge member
      rw [leafChildren] at member
      have which : b=0 ∨ b=1 := by omega
      rcases which with rfl|rfl
      · have cases : edge=(some downId,0) ∨ edge=(none,1) := by simpa using member
        rcases cases with rfl|rfl
        · exact leafEdge
        · intro next equal; cases equal
      · have cases : edge=(none,0) ∨ edge=(some downId,1) := by simpa using member
        rcases cases with rfl|rfl
        · intro next equal; cases equal
        · exact leafEdge
  · have distinct : (fresh::s.nodes.flatMap nodeChildren).Nodup :=
      List.nodup_cons.mpr ⟨heap_child_fresh checked absent,heap_children_nodup checked⟩
    have changed := (children_replaceChild_perm unique parent shape bit occupied).symm.nodup distinct
    have leafList : nodeChildren (fresh,leaf)=[downId] := by
      have which : b=0 ∨ b=1 := by omega
      rcases which with rfl|rfl <;> simp [nodeChildren,leafChildren,edgeChildren]
    simpa only [attachedChild,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      leafList,List.append_nil] using changed

#print axioms heap_spliced_child
end Binary.Pair.Trie.C1Cover
