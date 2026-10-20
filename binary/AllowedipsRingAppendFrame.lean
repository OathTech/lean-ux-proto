import AllowedipsFocus

namespace Binary.Pair.Allowedips.Ring

/-- Only the affected list words need framing. Other registered nodes may be
changed; the decoder follows the already-established finite chain. -/
theorem append_frame {names o m head last added other fuel entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (lastSlot : LinkSlot names last)
    (addedSlot : LinkSlot names added) (otherSlot : LinkSlot names other)
    (headApart : other≠head) (lastApart : other≠last) (addedApart : other≠added)
    (decoded : (do
      let first ← word m "peer.list.head" other 8
      peerList names m other fuel first other [])=.ok entries)
    (nodeApart : ∀ nodes : Nodes, entries=nodes.map Prod.snd →
      Chain names m other other nodes → ∀ link ∈ nodes.map Prod.fst,
        link≠head ∧ link≠last ∧ link≠added) :
    (do
      let first ← word (appendMemory m head last added) "peer.list.head" other 8
      peerList names (appendMemory m head last added) other fuel first other [])=.ok entries := by
  obtain ⟨firstWord,firstRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,_⟩ := peerList_shape run
  have parts := nodeApart nodes entriesEq shape
  have changed : ∀ previous rest, Chain names m other previous rest →
      rest ⊆ nodes → Chain names (appendMemory m head last added) other previous rest := by
    intro previous rest chain
    induction chain with
    | nil close =>
      intro _
      apply Chain.nil
      rw [append_back g layout headSlot lastSlot addedSlot otherSlot]
      simp only [addedApart,headApart,ite_false,close]
    | @cons previous link id rest fields tail ih =>
      intro subset
      have member : (link,id) ∈ nodes := subset (by simp)
      obtain ⟨headNe,lastNe,addedNe⟩ := parts link (List.mem_map.mpr ⟨(link,id),member,rfl⟩)
      apply Chain.cons (id:=id)
      · refine ⟨fields.known,fields.notHead,fields.valid,fields.owner,?_,?_⟩
        · rw [append_back g layout headSlot lastSlot addedSlot fields.slot]
          simp only [addedNe,headNe,ite_false,fields.back]
        · rw [append_forward g layout headSlot lastSlot addedSlot fields.slot]
          simp only [lastNe,addedNe,ite_false,fields.forward]
      · exact ih (fun _ member => subset (List.mem_cons_of_mem _ member))
  have result := (changed _ _ shape (fun _ member => member)).decode fuel [] length distinct (by simp)
  rw [append_forward g layout headSlot lastSlot addedSlot otherSlot]
  simp only [lastApart,addedApart,ite_false,firstRead]
  change peerList names (appendMemory m head last added) other fuel firstWord other []=_
  simpa only [headEq,entriesEq] using result

theorem Fields.same_link {names m head p link q id head' p' q' id'}
    (left : Fields names m head p link q id) (right : Fields names m head' p' link q' id') : id=id' :=
  Option.some.inj (Except.ok.inj (left.owner.symm.trans right.owner))

/-- Distinct ownership lists remain unchanged by append to the destination.
Disjointness is about decoded identities and will come from the heap's exact
ownership check, not a new pointer-separation assumption. -/
theorem append_other {names o m head last added other fuel entries destination id p q pid peer}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (headPeer : (pid,peer) ∈ names.trie.peers) (headEq : head=peer+1096)
    (otherSlot : LinkSlot names other)
    (focus : Fields names m other p added q id)
    (headApart : other≠head)
    (otherNode : ∀ nodeId base, (nodeId,base) ∈ names.trie.nodes → base+56≠other)
    (tailRead : word m "peer.list.prev" (head+8) 8=.ok last)
    (target : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok destination)
    (decoded : (do
      let first ← word m "peer.list.head" other 8
      peerList names m other fuel first other [])=.ok entries)
    (disjoint : ∀ id, id ∈ destination → id ∉ entries) (fresh : id ∉ entries) :
    (do
      let first ← word (appendMemory m head last added) "peer.list.head" other 8
      peerList names (appendMemory m head last added) other fuel first other [])=.ok entries := by
  have lastSlot := decoded_tail_slot headSlot target tailRead
  obtain ⟨firstWord,_,run⟩ := bind_ok target
  obtain ⟨targetNodes,targetEq,_,targetShape,_,_,_⟩ := peerList_shape run
  have lastOrigin := targetShape.last_origin tailRead
  have lastApart : other≠last := by
    intro equal
    rcases lastOrigin with root|member
    · exact headApart (equal.trans root)
    · obtain ⟨⟨link,current⟩,present,location⟩ := List.mem_map.mp member
      obtain ⟨p,q,fields⟩ := targetShape.member_fields present
      have valid : 56≤link := fields.valid
      have linkEq : link-56+56=link := by omega
      exact otherNode current (link-56) fields.named (linkEq.trans (location.trans equal.symm))
  apply append_frame g layout headSlot lastSlot focus.slot otherSlot headApart lastApart (Ne.symm focus.notHead) decoded
  intro nodes entriesEq shape link member
  obtain ⟨⟨address,current⟩,present,location⟩ := List.mem_map.mp member
  obtain ⟨p,q,fields⟩ := shape.member_fields present
  dsimp only at location
  subst address
  have inEntries : current ∈ entries := by rw [entriesEq]; exact List.mem_map.mpr ⟨(link,current),present,rfl⟩
  have headNe : link≠head := by
    have ne := node_peer_link_ne g layout fields.named headPeer
    have valid : 56≤link := fields.valid
    have linkEq : link-AllowedipsMutationLayout.peer_list+56=link := by change link-56+56=link; omega
    simpa only [linkEq,←headEq] using ne
  refine ⟨headNe,?_,?_⟩
  · intro equal
    rcases lastOrigin with root|member
    · exact headNe (equal.trans root)
    · obtain ⟨⟨targetLink,targetId⟩,present,targetLocation⟩ := List.mem_map.mp member
      obtain ⟨p,q,targetFields⟩ := targetShape.member_fields present
      have same : targetLink=link := targetLocation.trans equal.symm
      subst targetLink
      have identity := fields.same_link targetFields
      have targetMember : current ∈ destination := by
        rw [targetEq]
        exact List.mem_map.mpr ⟨(link,targetId),present,identity.symm⟩
      exact disjoint current targetMember inEntries
  · intro equal
    subst added
    exact fresh ((fields.same_link focus) ▸ inEntries)

#print axioms append_other
end Binary.Pair.Allowedips.Ring
