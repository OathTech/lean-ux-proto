import AllowedipsInternalFrame

namespace Binary.Pair.Allowedips.Exact
open Leanux Leanux.WG

theorem effect_internal {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : effect s=.ok (memory,regs))
    (current : NodeId) (other : AipNode) (member : (current,other) ∈ (target d).nodes)
    (different : current≠id) (internal : other.peer=none) : internalListCheck names memory current=.ok () := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  obtain ⟨previous,next,focus,previousSlot,nextSlot,predecessor,successor⟩ := focus_of_heap related shape named present peerNamed
  have back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous := by
    simpa only [nodeAt,Nat.add_assoc] using focus.back
  have forward : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok next := by simpa only [nodeAt] using focus.forward
  obtain ⟨last,tailRead,memoryEq⟩ := effect_ring g layout (.peer peerNamed) (by simpa only [nodeAt] using focus.slot)
    (by rw [peerAt]) back forward checked
  simp only [nodeAt,peerAt] at tailRead memoryEq
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers := by
    exact List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have removed := Ring.owner_unlink_decodes g layout (.peer peerNamed) previousSlot nextSlot core.nodeIds focus
    predecessor successor (Reconstructed.peer_at related peerNamed ownerMember) (value:=peer)
  simp only [Nat.add_sub_cancel] at removed
  obtain ⟨otherBase,otherNamed,_⟩ := (reconstruct_fields related).node member
  have fields := internal_fields related otherNamed peerNamed ((heap_ownership shape current other member).2 internal)
  have distinctLinks : otherBase+56≠base+56 := fun equal => different ((fields.identity_iff focus core.nodeIds).mpr equal)
  have words := Ring.reassign_internal g layout (.peer peerNamed) previousSlot nextSlot focus fields distinctLinks
    predecessor successor (value:=peer) (by simpa only [Nat.add_sub_cancel] using removed)
    (by simpa only [Nat.add_sub_cancel] using tailRead)
  simp only [Nat.add_sub_cancel] at words
  rw [memoryEq]
  exact internalListCheck_of_words core.nodeIds otherNamed words.1 (by simpa only [Nat.add_assoc] using words.2)

#print axioms effect_internal
end Binary.Pair.Allowedips.Exact
