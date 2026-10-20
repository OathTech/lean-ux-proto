import AllowedipsFocusNames

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem internal_fields {names o m d id base pid peer}
    (related : Corresponds names o m d) (named : (id,base) ∈ names.trie.nodes)
    (peerNamed : (pid,peer) ∈ names.trie.peers)
    (checked : internalListCheck names m id=.ok ()) :
    Ring.Fields names m (peer+1096) (base+56) (base+56) (base+56) id := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  have location : Trie.address names.trie.nodes (some id)=.ok base := by
    simp only [Trie.address,Trie.find_identity core.nodeIds named]
    rfl
  unfold internalListCheck at checked
  obtain ⟨address,read,checked⟩ := bind_ok checked
  have equal : address=base := Except.ok.inj (read.symm.trans location)
  subst address
  obtain ⟨next,nextRead,checked⟩ := bind_ok checked
  obtain ⟨previous,previousRead,checked⟩ := bind_ok checked
  obtain ⟨links,_⟩ := check_ok _ _ _ _ checked
  have links : next=base+56 ∧ previous=base+56 := by
    simpa only [Bool.and_eq_true,beq_iff_eq,AllowedipsMutationLayout.peer_list] using links
  rcases links with ⟨rfl,rfl⟩
  refine ⟨?_,node_peer_link_ne g layout named peerNamed,by change 56≤base+56; omega,?_,?_,?_⟩
  · apply List.any_eq_true.mpr
    exact ⟨(id,base),named,by simp [AllowedipsMutationLayout.peer_list]⟩
  · simpa only [AllowedipsMutationLayout.peer_list,Nat.add_sub_cancel] using
      pointer_named (node_addresses related) named (core.nodeRange id base named).1 "peer.list.node"
  · apply Trie.word_of_loadInt
    · have := (core.nodeRange id base named).2
      rw [layout] at this
      omega
    · exact Trie.readNat_loadInt previousRead
  · apply Trie.word_of_loadInt
    · have := (core.nodeRange id base named).2
      rw [layout] at this
      omega
    · exact Trie.readNat_loadInt nextRead

/-- Every focus's neighbor facts come from entry reconstruction plus the
existing ownership check. Internal NULL-owner nodes use their checked self
links; owned nodes use the finite decoded owner ring. -/
theorem focus_of_heap {names o m d id base node pid peer}
    (related : Corresponds names o m d) (checked : heap names (target d) m=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) :
    ∃ previous next,
      Ring.Fields names m (peer+1096) previous (base+56) next id ∧
      LinkSlot names previous ∧ LinkSlot names next ∧
      word m "unlink.predecessor" previous 8=.ok (base+56) ∧
      word m "peer.list.prev" (next+8) 8=.ok (base+56) := by
  have core := Trie.reconstruct_fields related.trie
  have full := reconstruct_fields related
  have member : (id,node) ∈ (target d).nodes := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present
  obtain ⟨ownership,internal⟩ := heap_ownership checked id node member
  cases owner : node.peer with
  | none =>
    have fields := internal_fields related named peerNamed (internal owner)
    exact ⟨base+56,base+56,fields,.node named,.node named,Binary.Pair.word_path fields.forward _,fields.back⟩
  | some owner =>
    rw [owner] at ownership
    obtain ⟨count,entries,peerMember,contains⟩ := owners_some ownership
    obtain ⟨ownerBase,ownerNamed,_,decoded⟩ := full.peer peerMember
    obtain ⟨firstWord,headRead,run⟩ := bind_ok decoded
    obtain ⟨nodes,entriesEq,headEq,shape,_,_,_⟩ := Ring.peerList_shape run
    have contains' : id ∈ nodes.map Prod.snd := entriesEq ▸ contains
    obtain ⟨⟨link,current⟩,nodeMember,identity⟩ := List.mem_map.mp contains'
    dsimp only at identity
    subst current
    obtain ⟨previous,next,fields⟩ := shape.member_fields nodeMember
    have location := Index.unique_first core.nodeIds fields.named named
    have valid : 56≤link := fields.valid
    have linkEq : link=base+56 := by
      change link-56=base at location
      omega
    have destination : link≠peer+1096 := by
      rw [linkEq]
      exact node_peer_link_ne (geometry related) core.layout.1 named peerNamed
    have enter : word m "peer.list.head" (ownerBase+1096) 8=.ok (Ring.first (ownerBase+1096) nodes) := by
      simpa only [headEq] using headRead
    refine ⟨previous,next,?_,shape.previous_slot (.peer ownerNamed) nodeMember fields,
      shape.next_slot (.peer ownerNamed) nodeMember fields,?_,?_⟩
    · simpa only [linkEq] using fields.rehead destination
    · simpa only [linkEq] using shape.predecessor_read nodeMember fields enter
    · simpa only [linkEq] using shape.successor_read nodeMember fields

#print axioms focus_of_heap
end Binary.Pair.Allowedips
