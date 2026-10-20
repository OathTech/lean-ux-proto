import AllowedipsAllocationNames

namespace Binary.Pair.Allowedips.Root

/-- A zeroed fresh allocation is appended to its owner's actual list. The
old decoder supplies both list freshness and the enlarged traversal budget;
the fresh node need not be self-linked before Linux initializes its links. -/
theorem append_allocated_list {names : Names} {o s memory pid entries}
    (g : Geometry (names.allocated s.regs.rbx.toNat) o) (layout : o.nodeSize=72)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (bounded : ∀ p ∈ names.trie.nodes, p.1<names.nextNode)
    (nonnull : s.regs.rbx.toNat≠0)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠s.regs.rbx.toNat)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList names s.dmem (s.regs.r14.toNat+1096) (names.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
    (appended : AppendEffect s memory) :
    (do
      let first ← word memory "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList (names.allocated s.regs.rbx.toNat) memory (s.regs.r14.toNat+1096)
        ((names.allocated s.regs.rbx.toNat).trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=
      .ok (entries++[names.nextNode]) := by
  let n := names.allocated s.regs.rbx.toNat
  have named : (names.nextNode,s.regs.rbx.toNat) ∈ n.trie.nodes := allocated_node names s.regs.rbx.toNat
  have peerNew : (pid,s.regs.r14.toNat) ∈ n.trie.peers := peerNamed
  have ids := allocated_ids s.regs.rbx.toNat unique bounded
  obtain ⟨first,firstRead,oldRun⟩ := bind_ok decoded
  have newList : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries := by
    rw [firstRead]
    exact Ring.peerList_allocate oldRun
  have absent : names.nextNode ∉ entries := Ring.peerList_fresh oldRun bounded
  have focus : Ring.Fields n s.dmem (s.regs.r14.toNat+1096) 0 (s.regs.rbx.toNat+56) 0 names.nextNode := by
    refine ⟨?_,node_peer_link_ne g layout named peerNew,?_,?_,?_,zeroNext⟩
    · exact List.any_eq_true.mpr ⟨(names.nextNode,s.regs.rbx.toNat),named,by simp [AllowedipsMutationLayout.peer_list]⟩
    · change 56≤s.regs.rbx.toNat+56; omega
    · simpa only [Nat.add_sub_cancel,AllowedipsMutationLayout.peer_list] using
        pointer_allocated "peer.list.node" nonnull fresh
    · simpa only [Nat.add_assoc] using zeroPrev
  let ownerMemory := write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat
  have ownerList := Ring.owner_decodes g layout (.peer peerNew) named newList (value:=s.regs.r14.toNat)
  have ownerFocus := focus.owner_frame g layout named (value:=s.regs.r14.toNat)
  obtain ⟨last,tailRead,memoryEq⟩ := appended
  have peerExtent := g.bounded _ (peer_allocation peerNew)
  change s.regs.r14.toNat+Layouts.peerSize≤2^64 at peerExtent
  have enough : 1112≤Layouts.peerSize := by decide
  have back : word ownerMemory "peer.list.prev" (s.regs.r14.toNat+1096+8) 8=.ok last := by
    apply Trie.word_of_loadInt _ (by omega)
    simpa only [Nat.add_assoc] using Trie.readNat_loadInt tailRead
  have lastSlot := Ring.decoded_tail_slot (.peer peerNew) ownerList back
  have budget := Ring.append_budget ownerFocus ids ownerList absent
  rw [memoryEq]
  exact Ring.append_decodes g layout (.peer peerNew) lastSlot ownerFocus back ownerList absent ids budget


theorem attach_allocated_list {names : Names} {o s memory cidr pid entries}
    (g : Geometry (names.allocated s.regs.rbx.toNat) o) (layout : o.nodeSize=72)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (bounded : ∀ p ∈ names.trie.nodes, p.1<names.nextNode)
    (nonnull : s.regs.rbx.toNat≠0)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠s.regs.rbx.toNat)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList names s.dmem (s.regs.r14.toNat+1096) (names.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
    (checked : attach s=.ok (memory,cidr)) :
    (do
      let first ← word memory "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList (names.allocated s.regs.rbx.toNat) memory (s.regs.r14.toNat+1096)
        ((names.allocated s.regs.rbx.toNat).trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=
      .ok (entries++[names.nextNode]) := by
  exact append_allocated_list g layout unique bounded nonnull fresh peerNamed decoded zeroNext zeroPrev (attach_as_ring checked)

#print axioms attach_allocated_list
end Binary.Pair.Allowedips.Root
