import AllowedipsChildStructure

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Root

theorem trieState_installedChild (s : State) (parentId direction key cidr width pid : Nat) :
    trieState (installedChild parentId direction key cidr width pid s)=
      Trie.attachedChild (trieState s) parentId direction s.nextNode
        (Trie.targetNode {newNode key cidr width (some pid) with parent:=.child parentId direction}) := by
  simp only [trieState,installedChild,Trie.attachedChild,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,appendOwner]
  congr 1
  congr 1
  apply List.map_congr_left
  rintro ⟨id,node⟩ _
  by_cases same : id=parentId <;> simp only [installChild,Trie.changeChild,same,ite_true,ite_false] <;> rfl

theorem target_node_unique (d : Device) : ((target d).nodes.map Prod.fst).Nodup := by
  change (d.nodes.toList.map Prod.fst).Nodup
  rw [Std.TreeMap.map_fst_toList_eq_keys]
  exact d.nodes.nodup_keys

/-- All parts of the executable allowed-IPs heap assertion are restored by
child attachment. Parent shape and freshness follow from the input relation;
the selected empty slot and its arithmetic facts are supplied by placement. -/
theorem heap_installedChild {names newNames o before after d}
    {parentId direction key cidr width pid : Nat} {parentNode : AipNode} (owner : Peer)
    (related : Corresponds names o before d) (checked : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner) (parent : (parentId,parentNode) ∈ (target d).nodes)
    (bit : direction<2) (empty : parentNode.bit[direction]?=some none)
    (sameWidth : width=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    heap newNames (installedChild parentId direction key cidr width pid (target d)) after=.ok () := by
  have below := target_nodes_below related
  have unique := target_node_unique d
  have checks := (heap_checks names (target d) before).mp checked
  obtain ⟨base,_,read⟩ := (reconstruct_fields related).node parent
  obtain ⟨left,right,_,_,shape,_⟩ := (Trie.decodeNode_fields (decodeNode_fields read).2).children
  change parentNode.bit=#[left,right] at shape
  apply (heap_checks newNames _ after).mpr
  constructor
  · change Trie.heap (trieState (installedChild parentId direction key cidr width pid (target d))) _=_
    rw [trieState_installedChild]
    apply Trie.heap_attached_child
      (leaf:=Trie.targetNode {newNode key cidr width (some pid) with parent:=.child parentId direction}) checks.1
      (by simpa only [trieState,List.map_map,Function.comp_def] using unique)
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (below old present))
      (List.mem_map.mpr ⟨(parentId,parentNode),parent,rfl⟩) shape bit empty rfl sameWidth measure prefixEq side
  · intro id node member
    refine ⟨?_,ownership_installedChild parentId direction key cidr width pid owner related checked hasPeer internal id node member⟩
    rcases List.mem_append.mp member with old | new
    · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
      cases equal
      exact (structureCheck_installedChild_old unique parent shape bit empty
        (Nat.ne_of_lt (below (current,original) present))).trans (checks.2 current original present).1
    · obtain equal := List.mem_singleton.mp new
      cases equal
      exact structureCheck_installedChild_new parentId direction key cidr width pid checked below unique parent shape bit empty

#print axioms heap_installedChild
end Binary.Pair.Allowedips
