import AllowedipsRootCopyDecode
import AllowedipsNamesExtension

namespace Binary.Pair.Allowedips.Root

/-- Common data effect of attaching an allocated record to its owner list.
Each compiled path proves this from its own ordered reads and stores. -/
def AppendEffect (s : MachineData) (memory : DataMem) : Prop :=
  ∃ last, readNat ⟨{s with dmem:=write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat},0⟩
      (s.regs.r14.toNat+1104) 8=.ok last ∧
    memory=Ring.appendMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat)
      (s.regs.r14.toNat+1096) last (s.regs.rbx.toNat+56)

/-- Invert the tested attachment phase into the existing ordered list-splice
effect. The tail is read after the owner store, as in the image. -/
theorem attach_as_ring {s : MachineData} {memory cidr}
    (checked : attach s=.ok (memory,cidr)) :
    ∃ last, readNat ⟨{s with dmem:=write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat},0⟩
      (s.regs.r14.toNat+1104) 8=.ok last ∧
      memory=Ring.appendMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat)
        (s.regs.r14.toNat+1096) last (s.regs.rbx.toNat+56) := by
  unfold attach at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨m1,ownerStore,checked⟩ := bind_ok checked
  obtain ⟨requested,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨last,tailRead,checked⟩ := bind_ok checked
  obtain ⟨m2,headStore,checked⟩ := bind_ok checked
  obtain ⟨m3,forwardStore,checked⟩ := bind_ok checked
  obtain ⟨m4,backStore,checked⟩ := bind_ok checked
  obtain ⟨m5,lastStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have ownerEq := (store_facts ownerStore).2
  have headEq := (store_facts headStore).2
  have forwardEq := (store_facts forwardStore).2
  have backEq := (store_facts backStore).2
  have lastEq := (store_facts lastStore).2
  rw [store_nat64] at ownerEq headEq forwardEq backEq lastEq
  refine ⟨last,?_,?_⟩
  · simpa only [ownerEq,write64] using tailRead
  · simp only [lastEq,backEq,forwardEq,headEq,ownerEq,Ring.appendMemory,write64,Nat.add_assoc]

/-- Attachment preserves the freshly zeroed child words and installs the
owner. Tail membership and separation follow from the existing decoded peer
list and allocation geometry; no independent tail-address premise is used. -/
theorem append_record_fields {names : Names} {o} {s : MachineData} {memory last id pid entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList names s.dmem (s.regs.r14.toNat+1096) (names.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries)
    (left : word s.dmem "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (tailRead : readNat ⟨{s with dmem:=write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat},0⟩
      (s.regs.r14.toNat+1104) 8=.ok last)
    (memoryEq : memory=Ring.appendMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat)
      (s.regs.r14.toNat+1096) last (s.regs.rbx.toNat+56)) :
    word memory "node.peer" s.regs.rbx.toNat 8=.ok s.regs.r14.toNat ∧
      word memory "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0 ∧
      word memory "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0 ∧
      EqualOutside (ListWrites names) (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) memory := by
  have nb := g.bounded _ (node_allocation named)
  have pb := g.bounded _ (peer_allocation peerNamed)
  change s.regs.rbx.toNat+o.nodeSize≤2^64 at nb
  change s.regs.r14.toNat+Layouts.peerSize≤2^64 at pb
  rw [layout] at nb
  have peerExtent : 1112≤Layouts.peerSize := by decide
  have back : word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat)
      "peer.list.prev" (s.regs.r14.toNat+1096+8) 8=.ok last := by
    apply Trie.word_of_loadInt _ (by omega)
    simpa only [Nat.add_assoc] using Trie.readNat_loadInt tailRead
  have oldList := Ring.owner_decodes g layout (.peer peerNamed) named decoded (value:=s.regs.r14.toNat)
  have lastSlot := Ring.decoded_tail_slot (.peer peerNamed) oldList back
  have frame : EqualOutside (ListWrites names)
      (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) memory := by
    rw [memoryEq]
    exact Ring.append_bytes_frame (.peer peerNamed) lastSlot (.node named)
  have keep (offset size : Nat) (within : offset+size≤56) (path : String) :
      word memory path (s.regs.rbx.toNat+offset) size=
        word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) path (s.regs.rbx.toNat+offset) size := by
    exact (Trie.word_frame frame path _ _ (node_before_list_apart g layout named within)).symm
  refine ⟨?_,?_,?_,frame⟩
  · have keepOwner := keep 0 8 (by decide) "node.peer"
    simp only [Nat.add_zero] at keepOwner
    rw [keepOwner]
    exact word_write64_same _ _ _ _ (by omega) s.regs.r14.toBitVec.isLt
  · rw [keep 8 8 (by decide) "node.child[0]"]
    rw [write64,←store_nat64]
    have framed := word_store_frame s.dmem "node.child[0]" s.regs.rbx.toNat 8 8 0 8 s.regs.r14.toNat
      (by decide) (by decide) (.inr (by decide))
    simpa only [Nat.add_zero,left] using framed
  · rw [keep 16 8 (by decide) "node.child[1]"]
    rw [write64,←store_nat64]
    have framed := word_store_frame s.dmem "node.child[1]" s.regs.rbx.toNat 16 8 0 8 s.regs.r14.toNat
      (by decide) (by decide) (.inr (by decide))
    simpa only [Nat.add_zero,right] using framed


theorem attach_record_fields {names : Names} {o s memory cidr id pid entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList names s.dmem (s.regs.r14.toNat+1096) (names.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries)
    (left : word s.dmem "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (checked : attach s=.ok (memory,cidr)) :
    word memory "node.peer" s.regs.rbx.toNat 8=.ok s.regs.r14.toNat ∧
      word memory "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0 ∧
      word memory "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0 ∧
      EqualOutside (ListWrites names) (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) memory := by
  obtain ⟨last,tailRead,memoryEq⟩ := attach_as_ring checked
  exact append_record_fields g layout named peerNamed decoded left right tailRead memoryEq

#print axioms attach_record_fields
end Binary.Pair.Allowedips.Root
