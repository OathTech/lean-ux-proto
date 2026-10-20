import AllowedipsRootMetadata
import AllowedipsRootOwners

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

/-- A self-linked internal node cannot be the tail of a decoded owner list.
Appending a fresh node therefore leaves both of its links unchanged. -/
theorem Ring.append_internal {names o m head last fresh id other current entries value}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (named : (id,fresh) ∈ names.trie.nodes)
    (internal : Ring.Fields names m head other other other current)
    (different : other≠fresh+56)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head (names.trie.nodes.length+1) first head [])=.ok entries)
    (tail : word (write64 m fresh value) "peer.list.prev" (head+8) 8=.ok last) :
    let after := Ring.appendMemory (write64 m fresh value) head last (fresh+56)
    word after "peer.list.next" other 8=.ok other ∧
      word after "peer.list.prev" (other+8) 8=.ok other := by
  have kept := internal.owner_frame g layout named (value:=value)
  have ownerList := Ring.owner_decodes g layout headSlot named decoded (value:=value)
  have lastSlot := Ring.decoded_tail_slot headSlot ownerList tail
  obtain ⟨first,firstRead,run⟩ := bind_ok ownerList
  obtain ⟨nodes,_,headEq,shape,_,_,_⟩ := Ring.peerList_shape run
  have enter : word (write64 m fresh value) "peer.list.next" head 8=.ok (Ring.first head nodes) :=
    Binary.Pair.word_path (headEq ▸ firstRead) _
  have lastForward := shape.last_forward enter tail
  have notLast : other≠last := by
    intro same
    rw [←same] at lastForward
    exact internal.notHead (word_values kept.forward lastForward)
  dsimp only
  constructor
  · rw [Ring.append_forward g layout headSlot lastSlot (.node named) kept.slot,
      ite_eq_right notLast,ite_eq_right different]
    exact kept.forward
  · rw [Ring.append_back g layout headSlot lastSlot (.node named) kept.slot,
      ite_eq_right different,ite_eq_right kept.notHead]
    exact kept.back

namespace Root

theorem attach_internal {names o s attached cidr d pid owner current node}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (g : Geometry (names.allocated s.regs.rbx.toNat) o)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠s.regs.rbx.toNat)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (checked : attach s=.ok (attached,cidr))
    (member : (current,node) ∈ (target d).nodes) (internal : node.peer=none) :
    internalListCheck (names.allocated s.regs.rbx.toNat) attached current=.ok () := by
  let n := names.allocated s.regs.rbx.toNat
  have core := Trie.reconstruct_fields related.trie
  have full := reconstruct_fields related
  have named : (names.nextNode,s.regs.rbx.toNat) ∈ n.trie.nodes := allocated_node names _
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  obtain ⟨address,oldNamed,_⟩ := full.node member
  have self := internal_fields related oldNamed peerNamed ((heap_ownership shape current node member).2 internal)
  have selfNew : Ring.Fields n s.dmem (s.regs.r14.toNat+1096) (address+56) (address+56) (address+56) current :=
    self.allocate
  have ownerList : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=
      .ok owner.allowedipsList := by
    obtain ⟨first,firstRead,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
    rw [firstRead]
    exact Ring.peerList_allocate run
  obtain ⟨last,tailRead,memoryEq⟩ := attach_as_ring checked
  have pb := g.bounded _ (peer_allocation (names:=n) peerNamed)
  change s.regs.r14.toNat+Layouts.peerSize≤2^64 at pb
  have enough : 1112≤Layouts.peerSize := by decide
  have back : word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) "peer.list.prev"
      (s.regs.r14.toNat+1096+8) 8=.ok last := by
    apply Trie.word_of_loadInt _ (by omega)
    simpa only [Nat.add_assoc] using Trie.readNat_loadInt tailRead
  have words := Ring.append_internal g core.layout.1 (.peer peerNamed) named selfNew
    (by have different := fresh (current,address) oldNamed; omega) ownerList back
  rw [memoryEq]
  exact internalListCheck_of_words (allocated_ids _ core.nodeIds (ids_below_counter full.valid))
    (List.mem_append_left _ oldNamed) words.1 (by simpa only [Nat.add_assoc] using words.2)

end Root
#print axioms Root.attach_internal
end Binary.Pair.Allowedips
