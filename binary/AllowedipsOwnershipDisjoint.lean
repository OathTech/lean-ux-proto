import AllowedipsRingAppendFrame

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem owners_member {s id pid count entries}
    (peer : (pid,count,entries) ∈ s.peers) (member : id ∈ entries) : pid ∈ owners s id := by
  apply List.mem_flatMap.mpr
  refine ⟨(pid,count,entries),peer,?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨id,member,by simp⟩

theorem Reconstructed.list_node {names o m s pid count entries id}
    (fields : Reconstructed names o m s)
    (peer : (pid,count,entries) ∈ s.peers) (member : id ∈ entries) :
    ∃ node, (id,node) ∈ s.nodes := by
  obtain ⟨base,_,_,decoded⟩ := fields.peer peer
  obtain ⟨first,_,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,_,shape,_,_,_⟩ := Ring.peerList_shape run
  have present : id ∈ nodes.map Prod.snd := entriesEq ▸ member
  obtain ⟨⟨link,current⟩,present,identity⟩ := List.mem_map.mp present
  obtain ⟨p,q,links⟩ := shape.member_fields present
  obtain ⟨⟨nodeId,node⟩,nodeMember,nodeRead⟩ := fields.nodes.left _ links.named
  have equal : current=nodeId := (decodeNode_fields nodeRead).1
  exact ⟨node,(equal.symm.trans identity) ▸ nodeMember⟩

/-- The executable ownership assertion excludes two distinct peers observing
the same node. This is derived, not an added separation clause in R. -/
theorem peer_lists_disjoint {names o m d left right count otherCount entries others}
    (related : Corresponds names o m d) (checked : heap names (target d) m=.ok ())
    (leftMember : (left,count,entries) ∈ (target d).peers)
    (rightMember : (right,otherCount,others) ∈ (target d).peers) (different : left≠right) :
    ∀ id, id ∈ entries → id ∉ others := by
  intro id member otherMember
  obtain ⟨node,present⟩ := (reconstruct_fields related).list_node leftMember member
  have owned := (heap_ownership checked id node present).1
  have leftOwner := owners_member leftMember member
  have rightOwner := owners_member rightMember otherMember
  rw [owned] at leftOwner rightOwner
  have l : node.peer=some left := by simpa using leftOwner
  have r : node.peer=some right := by simpa using rightOwner
  exact different (Option.some.inj (l.symm.trans r))

theorem peer_heads_ne {names o m d pid base other peer}
    (related : Corresponds names o m d) (named : (pid,base) ∈ names.trie.peers)
    (otherNamed : (other,peer) ∈ names.trie.peers) (different : pid≠other) : base+1096≠peer+1096 := by
  intro equal
  have bases : base=peer := Nat.add_right_cancel equal
  subst peer
  have first := find_address (name_addresses related).2 named
  have second := find_address (name_addresses related).2 otherNamed
  exact different (congrArg Prod.fst (Option.some.inj (first.symm.trans second)))

#print axioms peer_lists_disjoint
end Binary.Pair.Allowedips
