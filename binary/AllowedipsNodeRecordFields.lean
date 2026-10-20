import AllowedipsNodeAttachRing

namespace Binary.Pair.Allowedips.NodeInit
open Root

def rootView (s : MachineData) (base : Nat) : MachineData :=
  {s with regs:={s.regs with rbx:=.ofNat base}}

/-- The tested nonempty attachment establishes the same data effect as root
attachment. Only proved byte frames and disjoint-store commutation are used. -/
theorem append_effect {names : Names} {o s memory base cidr id pid}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,base) ∈ names.trie.nodes)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (checked : attach s=.ok (memory,base,cidr)) : AppendEffect (rootView s base) memory := by
  obtain ⟨last,tailRead,memoryEq⟩ := attach_as_ring checked
  have nb := g.bounded _ (node_allocation named)
  have pb := g.bounded _ (peer_allocation peerNamed)
  change base+o.nodeSize≤2^64 at nb
  change s.regs.r14.toNat+Layouts.peerSize≤2^64 at pb
  rw [layout] at nb
  have baseNat : (UInt64.ofNat base).toNat=base := by
    exact Nat.mod_eq_of_lt (by omega)
  have peerExtent : 1112≤Layouts.peerSize := by decide
  have tail : word s.dmem "peer.list.prev" (s.regs.r14.toNat+1096+8) 8=.ok last := by
    apply Trie.word_of_loadInt _ (by omega)
    simpa only [Nat.add_assoc,Nat.reduceAdd] using Trie.readNat_loadInt tailRead
  have ownerTail : word (write64 s.dmem base s.regs.r14.toNat) "peer.list.prev"
      (s.regs.r14.toNat+1096+8) 8=.ok last := by
    rw [Ring.owner_word_frame g layout (.peer peerNamed) named 8 (.inr rfl)]
    exact tail
  have tailAfter : readNat ⟨{s with dmem:=write64 s.dmem base s.regs.r14.toNat},0⟩
      (s.regs.r14.toNat+1104) 8=.ok last := by
    simpa only [readNat,Nat.add_assoc,Nat.reduceAdd] using readNat_of_word ownerTail
  refine ⟨last,?_,?_⟩
  · simpa only [rootView,baseNat,readNat] using tailAfter
  · simpa only [rootView,baseNat] using memoryEq

/-- Reuse root attachment's record/list lemma after proving the differing
store order equivalent. The early tail read is framed across the owner store. -/
theorem attach_record_fields {names : Names} {o s memory base cidr id pid entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,base) ∈ names.trie.nodes)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList names s.dmem (s.regs.r14.toNat+1096) (names.trie.nodes.length+1)
        first (s.regs.r14.toNat+1096) [])=.ok entries)
    (left : word s.dmem "node.child[0]" (base+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (base+16) 8=.ok 0)
    (checked : attach s=.ok (memory,base,cidr)) :
    word memory "node.peer" base 8=.ok s.regs.r14.toNat ∧
      word memory "node.child[0]" (base+8) 8=.ok 0 ∧
      word memory "node.child[1]" (base+16) 8=.ok 0 ∧
      EqualOutside (ListWrites names) (write64 s.dmem base s.regs.r14.toNat) memory := by
  have nb := g.bounded _ (node_allocation named)
  change base+o.nodeSize≤2^64 at nb
  rw [layout] at nb
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt (by omega)
  obtain ⟨last,tailRead,memoryEq⟩ := append_effect g layout named peerNamed checked
  have result := Root.append_record_fields (s:=rootView s base) g layout
    (by simpa only [rootView,baseNat] using named) peerNamed decoded
    (by simpa only [rootView,baseNat] using left) (by simpa only [rootView,baseNat] using right)
    tailRead memoryEq
  simpa only [rootView,baseNat] using result

#print axioms attach_record_fields
end Binary.Pair.Allowedips.NodeInit
