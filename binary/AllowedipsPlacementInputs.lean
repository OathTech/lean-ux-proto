import AllowedipsPlacementSimulation
import AllowedipsPlacementLocals
import PairTrieReadProof

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsRelation

theorem nodeRead_cover {names o a} (read : Trie.NodeReadBytes names.trie o a) :
    ∃ span ∈ readSpans names o, span.contains a := by
  obtain ⟨id,address,named,offset,size,field,inside⟩ := read
  refine ⟨(address+offset,size),?_,inside⟩
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨(id,address),named,List.mem_map.mpr ⟨(offset,size),List.mem_append_left _ field,rfl⟩⟩))

/-- All per-node execution facts are decoded from one related heap. The
physical loop does not acquire new assumptions on visiting another node. -/
theorem inputs_of_heap {names o d base pc c root key cidr bits peer stack acc}
    (related : Corresponds names o base.dmem d)
    (heap : TrieHeap base.dmem (Trie.interpretation names.trie.nodes) (Trie.interpretation names.trie.peers)
      (fun id => d.nodes.get? id) root bits key)
    (locals : LocalFields names ⟨base,pc⟩ key cidr bits peer stack acc)
    (cidrBound : cidr≤bits)
    (apart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬Writes base.regs.rsp c a)
    (queryApart : ∀ a, InRange base.regs.r13.toBitVec (bits/8) a → ¬Writes base.regs.rsp c a)
    (saved : SavedInput base c (.ofNat 32 bits) (.ofNat 64 peer)) :
    Inputs base c (Trie.interpretation names.trie.nodes) (Source.Aip.store d) root key cidr bits (.ofNat 64 peer) := by
  have nodeApart (id : NodeId) (node : AipNode)
      (reached : Reached (fun id => d.nodes.get? id) root bits key id)
      (present : d.nodes.get? id=some node) (a : BitVec 64)
      (read : NodeReads (Trie.interpretation names.trie.nodes) bits key id node a) :
      ¬Writes base.regs.rsp c a := by
    obtain ⟨span,member,inside⟩ := nodeRead_cover
      (names := names) (Trie.trieReads_nodeDecoded related.trie ⟨id,node,reached,present,read⟩)
    exact apart span member a inside
  refine ⟨saved,?_,?_⟩
  · intro id node reached present
    obtain ⟨actual,present',fields⟩ := heap.2.2 id reached
    have eq : actual=node := Option.some.inj (present'.symm.trans present)
    subst actual
    refine ⟨heap.1,locals.bitsValue,locals.cidrValue,cidrBound,fields.2.1,?_,?_,?_,?_,locals.query,queryApart⟩
    · exact fields.2.2.2.1
    · intro a read
      exact nodeApart id node reached present a (.inr (.inl read))
    · exact fields.2.2.1
    · intro a read
      exact nodeApart id node reached present a (.inl read)
  · intro id node next reached present matching short selected
    obtain ⟨actual,present',fields⟩ := heap.2.2 id reached
    have eq : actual=node := Option.some.inj (present'.symm.trans present)
    subst actual
    obtain ⟨width,_,byteRead,shiftRead,children⟩ := (fields.2.2.2.2 matching).2.2 short
    obtain ⟨childRead,nonnull⟩ := children next selected
    refine ⟨⟨heap.1,short,byteRead,shiftRead,?_,?_,locals.query,queryApart⟩,nonnull⟩
    · simpa only [childIndex,width,AllowedipsLayout.bit,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,BitVec.ofNat_add,←BitVec.add_assoc,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl,show BitVec.ofNat 64 25=(25 : BitVec 64) from rfl,show BitVec.ofNat 64 26=(26 : BitVec 64) from rfl] using childRead
    · intro a read
      apply nodeApart id node reached present a
      refine .inr (.inr ⟨matching,.inr ⟨short,?_⟩⟩)
      simpa only [childIndex,width,AllowedipsLayout.bit,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,BitVec.ofNat_add,←BitVec.add_assoc,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl,show BitVec.ofNat 64 25=(25 : BitVec 64) from rfl,show BitVec.ofNat 64 26=(26 : BitVec 64) from rfl] using read

#print axioms inputs_of_heap
end Binary.Pair.Allowedips.Placement
