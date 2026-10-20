import AllowedipsTrieChildFacts

namespace Binary.Pair.Trie
open Leanux Leanux.WG

theorem heap_child_fresh {s : State} {roots : List (Option NodeId)} {fresh : Nat}
    (checked : heap s roots=.ok ()) (absent : ∀ entry ∈ s.nodes, entry.1≠fresh) :
    fresh ∉ s.nodes.flatMap nodeChildren := by
  intro member
  obtain ⟨⟨id,node⟩,atNode,atChildren⟩ := List.mem_flatMap.mp member
  obtain ⟨edge,atEdge,atChild⟩ := List.mem_flatMap.mp atChildren
  have equal : edge.1=some fresh := by simpa [edgeChildren] using atChild
  obtain ⟨child,found,_⟩ := heap_edge_facts checked id node atNode edge atEdge fresh equal
  exact absent (fresh,child) (List.mem_of_find?_eq_some found) rfl

/-- Attaching one fresh leaf at a previously empty slot preserves the actual
executable graph assertion, including unique parents and both roots. -/
theorem heap_attached_child {s : State} {roots : List (Option NodeId)}
    {parentId direction fresh : Nat} {parentNode leaf : Node} {left right : Option Nat}
    (checked : heap s roots=.ok ()) (unique : (s.nodes.map Prod.fst).Nodup)
    (absent : ∀ entry ∈ s.nodes, entry.1≠fresh) (parent : (parentId,parentNode) ∈ s.nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (empty : parentNode.children[direction]?=some none) (noChildren : leaf.children=#[none,none])
    (width : leaf.width=parentNode.width) (measure : parentNode.cidr<leaf.cidr)
    (prefixEq : leaf.key/2^(parentNode.width-parentNode.cidr)=parentNode.key/2^(parentNode.width-parentNode.cidr))
    (side : leaf.key/2^(parentNode.width-1-parentNode.cidr)%2=direction) :
    heap (attachedChild s parentId direction fresh leaf) roots=.ok () := by
  have notRoot : some fresh ∉ roots := by
    intro root
    obtain ⟨node,member⟩ := heap_root checked root
    exact absent (fresh,node) member rfl
  have newEdge : EdgeFacts (attachedChild s parentId direction fresh leaf) roots parentNode (some fresh,direction) := by
    intro next equal
    cases Option.some.inj equal
    exact ⟨leaf,find_attached_fresh absent parentId direction leaf,notRoot,width,measure,prefixEq,side⟩
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
        simpa only [changeChild,ite_true] using edgeFacts_set_empty shape bit empty oldEdges newEdge
      · simpa only [changeChild,ite_eq_right same] using oldEdges
    · obtain equal := List.mem_singleton.mp new
      cases equal
      intro edge member next equal
      have edgeNone : edge.1=none := by
        have member := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member)
        simpa [noChildren] using member
      rw [edgeNone] at equal
      cases equal
  · have distinct : (fresh::s.nodes.flatMap nodeChildren).Nodup :=
      List.nodup_cons.mpr ⟨heap_child_fresh checked absent,heap_children_nodup checked⟩
    have changed := (children_changeChild_perm unique parent shape bit empty).symm.nodup distinct
    have leafChildren : nodeChildren (fresh,leaf)=[] := by simp [nodeChildren,noChildren,edgeChildren]
    simpa only [attachedChild,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      leafChildren,List.nil_append,List.append_nil] using changed

#print axioms heap_attached_child
end Binary.Pair.Trie
