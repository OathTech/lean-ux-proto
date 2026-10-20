import AllowedipsExactInternal

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem trieState_reassign (s : State) (focus pid : Nat) :
    trieState (reassign focus pid s)=
      {trieState s with nodes := (trieState s).nodes.map (fun (id,n) =>
        (id,{n with peer := if id=focus then some pid else n.peer}))} := by
  unfold trieState reassign
  congr 1
  · simp only [List.map_map]
    apply List.map_congr_left
    rintro ⟨id,n⟩ _
    by_cases same : id=focus <;> simp [reassignNode,Trie.targetNode,same]
  · simp only [List.map_map]
    rfl

theorem ownershipCheck_of {names s m id node}
    (owned : owners s id=node.peer.toList)
    (internal : node.peer=none → internalListCheck names m id=.ok ()) :
    ownershipCheck names s m id node=.ok () := by
  unfold ownershipCheck
  rw [owned]
  simp only [beq_self_eq_true,ite_true]
  cases h : node.peer with
  | none => exact internal h
  | some pid => rfl

/-- Ownership mutation preserves the structural assertion; the only physical
obligation is the self-ring check for other internal nodes. -/
theorem heap_reassign {names before after d focus pid peer}
    (checked : heap names (target d) before=.ok ())
    (present : d.peers.get? pid=some peer)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → current≠focus →
      node.peer=none → internalListCheck names after current=.ok ()) :
    heap names (reassign focus pid (target d)) after=.ok () := by
  obtain ⟨tree,nodes⟩ := (heap_checks names (target d) before).mp checked
  apply (heap_checks names _ after).mpr
  constructor
  · change Trie.heap (trieState (reassign focus pid (target d))) [d.peerAllowedips.root4,d.peerAllowedips.root6]=.ok ()
    rw [trieState_reassign,Trie.heap_mapPeer (trieState (target d))
      [d.peerAllowedips.root4,d.peerAllowedips.root6] (fun current owner => if current=focus then some pid else owner)]
    exact tree
  · intro current node member
    obtain ⟨⟨id,old⟩,original,equal⟩ := List.mem_map.mp member
    cases equal
    have oldShape := (nodes id old original).1
    have oldOwned := (heap_ownership checked id old original).1
    by_cases same : id=focus
    · simp only [same,ite_true]
      constructor
      · exact (structureCheck_mapPeer (target d) focus pid focus old).trans (same ▸ oldShape)
      · apply ownershipCheck_of
        · exact owners_reassign_target_focus d focus pid peer present
        · simp
    · simp only [same,ite_false]
      constructor
      · exact (structureCheck_mapPeer (target d) focus pid id old).trans oldShape
      · apply ownershipCheck_of
        · rw [owners_reassign_other _ _ _ _ same]
          exact oldOwned
        · exact internal id old original same

theorem Exact.effect_heap {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : Exact.effect s=.ok (memory,regs)) :
    heap names (reassign id pid (target d)) memory=.ok () :=
  heap_reassign shape hasPeer
    (Exact.effect_internal related shape named present peerNamed hasPeer nodeAt peerAt checked)

#print axioms Exact.effect_heap
end Binary.Pair.Allowedips
