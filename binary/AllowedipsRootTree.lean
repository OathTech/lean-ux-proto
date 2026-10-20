import AllowedipsTrieLeaf
import AllowedipsAllocationTarget

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps

theorem roots_below {s : State} {names m}
    (shape : heap names s m=.ok ()) (below : ∀ pair ∈ s.nodes, pair.1<s.nextNode) :
    ∀ id, some id ∈ [s.table.root4,s.table.root6] → id<s.nextNode := by
  have tree := ((heap_checks names s m).mp shape).1
  intro id present
  obtain ⟨node,member⟩ := Trie.heap_root tree present
  obtain ⟨⟨oldId,oldNode⟩,member,same⟩ := List.mem_map.mp member
  have sameId : oldId = id := congrArg Prod.fst same
  exact sameId ▸ below (oldId,oldNode) member

theorem edges_below {s : State} {names m}
    (shape : heap names s m=.ok ()) (below : ∀ pair ∈ s.nodes, pair.1<s.nextNode) :
    ∀ id node, (id,node) ∈ s.nodes → ∀ next, some next ∈ node.bit.toList → next<s.nextNode := by
  have tree := ((heap_checks names s m).mp shape).1
  intro id node present next child
  obtain ⟨target,member,_⟩ := Trie.heap_edges tree id (Trie.targetNode node)
    (List.mem_map.mpr ⟨(id,node),present,rfl⟩) next child
  obtain ⟨⟨oldId,oldNode⟩,member,same⟩ := List.mem_map.mp member
  have sameId : oldId = next := congrArg Prod.fst same
  exact sameId ▸ below (oldId,oldNode) member

theorem trie_heap_installed {s : State} {names m} (v4 : Bool) (key cidr pid : Nat)
    (shape : heap names s m=.ok ()) (below : ∀ pair ∈ s.nodes, pair.1<s.nextNode)
    (empty : (if v4 then s.table.root4 else s.table.root6)=none) :
    Trie.heap (trieState (installedRoot v4 key cidr pid s))
      [(installedRoot v4 key cidr pid s).table.root4,(installedRoot v4 key cidr pid s).table.root6]=.ok () := by
  have tree := ((heap_checks names s m).mp shape).1
  have core : Trie.heap
      { trieState s with nodes := (trieState s).nodes++[(s.nextNode,
        Trie.targetNode {newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4})] }
      [(installedRoot v4 key cidr pid s).table.root4,(installedRoot v4 key cidr pid s).table.root6]=.ok () := by
    apply Trie.heap_append_leaf tree rfl
    · intro id node member
      obtain ⟨⟨oldId,oldNode⟩,present,same⟩ := List.mem_map.mp member
      have sameId : oldId=id := congrArg Prod.fst same
      have bound : id<s.nextNode := sameId ▸ below (oldId,oldNode) present
      have different : id≠s.nextNode := Nat.ne_of_lt bound
      cases v4 <;> simp_all [installedRoot]
    · intro id member
      have rootMember : id=s.nextNode ∨ some id ∈ [s.table.root4,s.table.root6] := by
        cases v4 <;> simp_all [installedRoot,or_comm]
      rcases rootMember with rfl | old
      · exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _)⟩
      · obtain ⟨node,present⟩ := Trie.heap_root tree old
        exact ⟨node,List.mem_append_left _ present⟩
  simpa only [trieState,installedRoot,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,appendOwner] using core

#print axioms trie_heap_installed
end Binary.Pair.Allowedips.Root
