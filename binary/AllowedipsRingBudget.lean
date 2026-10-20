import AllowedipsRingAppend

namespace Binary.Pair.Allowedips.Ring

theorem decoded_tail_slot {names m head fuel entries last}
    (headSlot : LinkSlot names head)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries)
    (back : word m "peer.list.prev" (head+8) 8=.ok last) : LinkSlot names last := by
  obtain ⟨firstWord,_,run⟩ := bind_ok decoded
  obtain ⟨nodes,_,_,shape,_,_,_⟩ := peerList_shape run
  rcases shape.last_origin back with equal|member
  · exact equal ▸ headSlot
  · obtain ⟨⟨link,id⟩,present,equal⟩ := List.mem_map.mp member
    obtain ⟨p,q,fields⟩ := shape.member_fields present
    exact equal ▸ fields.slot

theorem Chain.links_named {names m head previous nodes}
    (shape : Chain names m head previous nodes) :
    nodes.map Prod.fst ⊆ names.trie.nodes.map (fun pair => pair.2+56) := by
  intro link member
  obtain ⟨⟨address,id⟩,present,equal⟩ := List.mem_map.mp member
  obtain ⟨p,q,fields⟩ := shape.member_fields present
  refine List.mem_map.mpr ⟨(id,address-56),fields.named,?_⟩
  have := fields.valid
  change 56≤address at this
  dsimp only at equal ⊢
  omega

/-- The existing interpretation supplies the traversal budget after append.
No fresh fuel premise is needed for a named node absent from the old list. -/
theorem append_budget {names m head fuel entries id added p q}
    (focus : Fields names m head p added q id)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries)
    (fresh : id ∉ entries) : entries.length+1<names.trie.nodes.length+1 := by
  obtain ⟨firstWord,_,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,_,shape,_,distinct,_⟩ := peerList_shape run
  have absent : added ∉ nodes.map Prod.fst := by
    intro present
    obtain ⟨⟨link,current⟩,member,equal⟩ := List.mem_map.mp present
    obtain ⟨p,q,fields⟩ := shape.member_fields member
    have identity := (fields.identity_iff focus unique).mpr equal
    exact fresh (entriesEq ▸ List.mem_map.mpr ⟨(link,current),member,identity⟩)
  have nd : (added::nodes.map Prod.fst).Nodup := List.nodup_cons.mpr ⟨absent,distinct⟩
  have sub : added::nodes.map Prod.fst ⊆ names.trie.nodes.map (fun pair => pair.2+56) := by
    intro link present
    rcases List.mem_cons.mp present with rfl|member
    · refine List.mem_map.mpr ⟨(id,link-56),focus.named,?_⟩
      have := focus.valid
      change 56≤link at this
      dsimp only
      omega
    · exact shape.links_named member
  have bound := nd.length_le_of_subset sub
  simp only [List.length_cons,List.length_map] at bound
  simpa only [entriesEq,List.length_map] using Nat.lt_succ_of_le bound

#print axioms append_budget
end Binary.Pair.Allowedips.Ring
