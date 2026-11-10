import C1BelowSplitCoverIncoming

/- Origin: trial source binary-trials/t5/T5TrieHeap.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 2a: the trie-level graph assertion after the intermediate
insertion: a fresh internal node spliced between `parent` and `down`, with a fresh
leaf as its other child. Obtained by composing t2's splice lemma with the landed
leaf attachment, then reordering the node list (the leaf was allocated first, so it
precedes the internal node in the names' order). -/
namespace Binary.Pair.Trie.C1Split
open Leanux Leanux.WG

/-- The graph assertion does not depend on the order of the node list. -/
theorem heap_perm {s : State} {roots : List (Option NodeId)} {nodes : List (NodeId×Node)}
    (checked : heap s roots=.ok ()) (unique : (nodes.map Prod.fst).Nodup)
    (perm : nodes.Perm s.nodes) : heap {s with nodes:=nodes} roots=.ok () := by
  apply heap_of_facts
  · intro id root
    obtain ⟨node,member⟩ := heap_root checked root
    exact ⟨node,perm.mem_iff.mpr member⟩
  · intro id node member edge atEdge next equal
    obtain ⟨child,found,rest⟩ :=
      heap_edge_facts checked id node (perm.mem_iff.mp member) edge atEdge next equal
    exact ⟨child,find_node_key unique (perm.mem_iff.mpr (List.mem_of_find?_eq_some found)),rest⟩
  · exact (perm.flatMap_right nodeChildren).nodup_iff.mpr (heap_children_nodup checked)

#print axioms heap_perm

theorem map_fst_changeChild (nodes : List (NodeId×Node)) (parentId direction fresh : Nat) :
    (nodes.map (changeChild parentId direction fresh)).map Prod.fst=nodes.map Prod.fst := by
  rw [List.map_map]
  apply List.map_congr_left
  intro entry _
  rfl

theorem heap_intermediate {s : State} {roots : List (Option NodeId)}
    {parentId direction leafId internalId downId b1 b2 : Nat}
    {parentNode downNode leaf internal : Node} {left right : Option Nat}
    (checked : heap s roots=.ok ()) (unique : (s.nodes.map Prod.fst).Nodup)
    (absentLeaf : ∀ entry ∈ s.nodes, entry.1≠leafId)
    (absentInternal : ∀ entry ∈ s.nodes, entry.1≠internalId)
    (distinct : leafId≠internalId)
    (parent : (parentId,parentNode) ∈ s.nodes) (down : (downId,downNode) ∈ s.nodes)
    (shape : parentNode.children=#[left,right]) (bit : direction<2)
    (occupied : parentNode.children[direction]?=some (some downId))
    (bit1 : b1<2) (bit2 : b2<2) (sides : b1≠b2)
    (internalChildren : internal.children=(#[none,none] : Array (Option NodeId)).set! b1 (some downId))
    (leafChildren : leaf.children=#[none,none])
    (width : internal.width=parentNode.width) (measure : parentNode.cidr<internal.cidr)
    (prefixEq : internal.key/2^(parentNode.width-parentNode.cidr)=
      parentNode.key/2^(parentNode.width-parentNode.cidr))
    (side : internal.key/2^(parentNode.width-1-parentNode.cidr)%2=direction)
    (downMeasure : internal.cidr<downNode.cidr)
    (downPrefix : downNode.key/2^(internal.width-internal.cidr)=internal.key/2^(internal.width-internal.cidr))
    (downSide : downNode.key/2^(internal.width-1-internal.cidr)%2=b1)
    (leafWidth : leaf.width=internal.width) (leafMeasure : internal.cidr<leaf.cidr)
    (leafPrefix : leaf.key/2^(internal.width-internal.cidr)=internal.key/2^(internal.width-internal.cidr))
    (leafSide : leaf.key/2^(internal.width-1-internal.cidr)%2=b2) :
    heap {s with nodes:=s.nodes.map (changeChild parentId direction internalId)++[(leafId,leaf)]++
      [(internalId,{internal with children:=internal.children.set! b2 (some leafId)})]} roots=.ok () := by
  have spliced := heap_spliced_child (fresh:=internalId) (leaf:=internal) checked unique absentInternal
    parent down shape bit occupied bit1 internalChildren width measure prefixEq side
    downMeasure downPrefix downSide
  have notLeaf : leafId ∉ s.nodes.map Prod.fst := by
    intro member
    obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
    exact absentLeaf entry present equal
  have notInternal : internalId ∉ s.nodes.map Prod.fst := by
    intro member
    obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
    exact absentInternal entry present equal
  have unique1 : ((attachedChild s parentId direction internalId internal).nodes.map Prod.fst).Nodup := by
    simp only [attachedChild,List.map_append,map_fst_changeChild,List.map_cons,List.map_nil]
    refine List.nodup_append.mpr ⟨unique,by simp,?_⟩
    intro a member b singleton equal
    have bEq : b=internalId := by simpa using singleton
    exact notInternal (bEq ▸ equal ▸ member)
  have absent1 : ∀ entry ∈ (attachedChild s parentId direction internalId internal).nodes, entry.1≠leafId := by
    intro entry member
    rcases List.mem_append.mp member with old|new
    · obtain ⟨original,present,rfl⟩ := List.mem_map.mp old
      exact absentLeaf original present
    · obtain rfl := List.mem_singleton.mp new
      exact Ne.symm distinct
  have which1 : b1=0 ∨ b1=1 := by omega
  have which2 : b2=0 ∨ b2=1 := by omega
  obtain ⟨l,r,shape1,empty1⟩ : ∃ l r, internal.children=#[l,r] ∧ internal.children[b2]?=some none := by
    rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl
    · exact absurd rfl sides
    · exact ⟨some downId,none,by simpa using internalChildren,by simp [internalChildren]⟩
    · exact ⟨none,some downId,by simpa using internalChildren,by simp [internalChildren]⟩
    · exact absurd rfl sides
  have attached := heap_attached_child (fresh:=leafId) (parentId:=internalId) (leaf:=leaf)
    spliced unique1 absent1 (List.mem_append_right _ (List.mem_singleton_self _)) shape1 bit2 empty1
    leafChildren leafWidth leafMeasure leafPrefix leafSide
  have final : (attachedChild (attachedChild s parentId direction internalId internal)
      internalId b2 leafId leaf).nodes=
      s.nodes.map (changeChild parentId direction internalId)++
        [(internalId,{internal with children:=internal.children.set! b2 (some leafId)})]++[(leafId,leaf)] := by
    simp only [attachedChild,List.map_append,List.map_cons,List.map_nil,List.map_map]
    congr 2
    · apply List.map_congr_left
      intro entry present
      have different : entry.1≠internalId := absentInternal entry present
      simp only [Function.comp_apply,changeChild,different,↓reduceIte]
    · simp only [changeChild,↓reduceIte]
  have uniqueFinal : ((s.nodes.map (changeChild parentId direction internalId)++[(leafId,leaf)]++
      [(internalId,{internal with children:=internal.children.set! b2 (some leafId)})]).map Prod.fst).Nodup := by
    simp only [List.map_append,map_fst_changeChild,List.map_cons,List.map_nil]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨unique,by simp,?_⟩,by simp,?_⟩
    · intro a member b singleton equal
      have bEq : b=leafId := by simpa using singleton
      exact notLeaf (bEq ▸ equal ▸ member)
    · intro a member b singleton equal
      have bEq : b=internalId := by simpa using singleton
      rcases List.mem_append.mp member with old|new
      · exact notInternal (bEq ▸ equal ▸ old)
      · have aEq : a=leafId := by simpa using new
        exact distinct (aEq ▸ equal.trans bEq)
  have result := heap_perm attached uniqueFinal (by
    rw [final,List.append_assoc,List.append_assoc]
    exact List.Perm.append_left _ (List.Perm.swap _ _ []))
  exact result

#print axioms heap_intermediate
end Binary.Pair.Trie.C1Split
