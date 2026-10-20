import AllowedipsRootAllocatedList
import AllowedipsExactLists

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

/-- Reconstruct every ownership list after the fresh-node attachment. The
other lists are framed using the existing heap's ownership invariant; their
separation is not added to the allocator or to the function precondition. -/
theorem append_lists {names o s memory d pid owner}
    (related : Corresponds names o s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (g : Geometry (names.allocated s.regs.rbx.toNat) o)
    (nonnull : s.regs.rbx.toNat≠0)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠s.regs.rbx.toNat)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
    (appended : AppendEffect s memory) :
    ∀ current address count entries, (current,address) ∈ names.trie.peers →
      (current,count,entries) ∈ (target d).peers →
      (do
        let first ← word memory "peer.list.head" (address+1096) 8
        peerList (names.allocated s.regs.rbx.toNat) memory (address+1096)
          ((names.allocated s.regs.rbx.toNat).trie.nodes.length+1) first (address+1096) [])=
        .ok (if current=pid then entries++[names.nextNode] else entries) := by
  let n := names.allocated s.regs.rbx.toNat
  have core := Trie.reconstruct_fields related.trie
  have layout : o.nodeSize=72 := core.layout.1
  have bounded := ids_below_counter (reconstruct_fields related).valid
  have named : (names.nextNode,s.regs.rbx.toNat) ∈ n.trie.nodes := allocated_node names _
  have peerNew : (pid,s.regs.r14.toNat) ∈ n.trie.peers := peerNamed
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have lifted (current address count entries) (currentNamed : (current,address) ∈ names.trie.peers)
      (member : (current,count,entries) ∈ (target d).peers) :
      (do
        let first ← word s.dmem "peer.list.head" (address+1096) 8
        peerList n s.dmem (address+1096) (n.trie.nodes.length+1) first (address+1096) [])=.ok entries := by
    obtain ⟨first,firstRead,run⟩ := bind_ok (Reconstructed.peer_at related currentNamed member)
    rw [firstRead]
    exact Ring.peerList_allocate run
  have ownerList := Ring.owner_decodes g layout (.peer peerNew) named
    (lifted pid _ _ _ peerNamed ownerMember) (value:=s.regs.r14.toNat)
  obtain ⟨last,tailRead,memoryEq⟩ := appended
  have pb := g.bounded _ (peer_allocation peerNew)
  change s.regs.r14.toNat+Layouts.peerSize≤2^64 at pb
  have enough : 1112≤Layouts.peerSize := by decide
  have back : word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat)
      "peer.list.prev" (s.regs.r14.toNat+1096+8) 8=.ok last := by
    apply Trie.word_of_loadInt _ (by omega)
    simpa only [Nat.add_assoc] using Trie.readNat_loadInt tailRead
  intro current address count entries currentNamed member
  by_cases same : current=pid
  · subst current
    have addressEq := Index.unique_first core.peerIds currentNamed peerNamed
    subst address
    simp only [ite_true]
    exact append_allocated_list g layout core.nodeIds bounded nonnull fresh peerNamed
      (Reconstructed.peer_at related peerNamed member) zeroNext zeroPrev ⟨last,tailRead,memoryEq⟩
  · simp only [same,ite_false]
    have currentNew : (current,address) ∈ n.trie.peers := currentNamed
    have focus : Ring.Fields n s.dmem (address+1096) 0 (s.regs.rbx.toNat+56) 0 names.nextNode := by
      refine ⟨?_,node_peer_link_ne g layout named currentNew,?_,?_,?_,zeroNext⟩
      · exact List.any_eq_true.mpr ⟨(names.nextNode,s.regs.rbx.toNat),named,by simp [AllowedipsMutationLayout.peer_list]⟩
      · change 56≤s.regs.rbx.toNat+56; omega
      · simpa only [Nat.add_sub_cancel,AllowedipsMutationLayout.peer_list] using
          pointer_allocated "peer.list.node" nonnull fresh
      · simpa only [Nat.add_assoc] using zeroPrev
    have otherList := Ring.owner_decodes g layout (.peer currentNew) named
      (lifted current address count entries currentNamed member) (value:=s.regs.r14.toNat)
    obtain ⟨_,_,oldRun⟩ := bind_ok (Reconstructed.peer_at related currentNamed member)
    rw [memoryEq]
    apply Ring.append_other g layout (.peer peerNew) peerNew rfl (.peer currentNew)
      (focus.owner_frame g layout named) (peer_heads_ne related currentNamed peerNamed same)
      (fun nodeId base member => node_peer_link_ne g layout member currentNew)
      back ownerList otherList
    · exact peer_lists_disjoint related heapOk ownerMember member (Ne.symm same)
    · exact Ring.peerList_fresh oldRun bounded


theorem attach_lists {names o s memory cidr d pid owner}
    (related : Corresponds names o s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (g : Geometry (names.allocated s.regs.rbx.toNat) o)
    (nonnull : s.regs.rbx.toNat≠0)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠s.regs.rbx.toNat)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
    (checked : attach s=.ok (memory,cidr)) :
    ∀ current address count entries, (current,address) ∈ names.trie.peers →
      (current,count,entries) ∈ (target d).peers →
      (do
        let first ← word memory "peer.list.head" (address+1096) 8
        peerList (names.allocated s.regs.rbx.toNat) memory (address+1096)
          ((names.allocated s.regs.rbx.toNat).trie.nodes.length+1) first (address+1096) [])=
        .ok (if current=pid then entries++[names.nextNode] else entries) := by
  exact append_lists related heapOk g nonnull fresh peerNamed hasPeer zeroNext zeroPrev (attach_as_ring checked)

#print axioms attach_lists
end Binary.Pair.Allowedips.Root
