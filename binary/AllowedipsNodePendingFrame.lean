import AllowedipsNodePending
import AllowedipsPlacementSimulation
import PairAllowedipsHeapFrame

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Root

/-- Stack and callback updates can carry the initialized but unpublished node
through correspondence cuts. The footprint is the existing executable read set;
it adds no clauses to R and assumes no intermediate reconstruction succeeds. -/
theorem Pending.frame {names : Names} {entry : MachineData} {d : WG.Device}
    {key cidr pid base : Nat} {before after : DataMem} {writes : BitVec 64 → Prop}
    (pending : Pending names entry d key cidr pid base before)
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬writes a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬writes a) :
    Pending names entry d key cidr pid base after := by
  let n := names.allocated base
  have metadataApart : ∀ span ∈ metadataSpans n nodeOffsets, ∀ a, span.contains a → ¬writes a :=
    fun span member => apart span (Placement.metadata_read member)
  have metadata := MetadataSame.of_frame n nodeOffsets same metadataApart
  have fresh := allocated_node names base
  have core : Trie.decodeNode n.trie nodeOffsets after base=Trie.decodeNode n.trie nodeOffsets before base := by
    apply Trie.decodeNode_congr
    intro offset size field path
    apply (Trie.word_frame same path _ _ _).symm
    apply apart (base+offset,size)
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨(names.nextNode,base),fresh,
        List.mem_map.mpr ⟨(offset,size),List.mem_append_left _ field,rfl⟩⟩))
  refine ⟨core.trans pending.core,?_,?_,?_,?_⟩
  · rintro ⟨id,address⟩ member value read
    rw [metadata.nodes id address (List.mem_append_left _ member)]
    exact pending.nodes (id,address) member value read
  · rintro ⟨id,address⟩ member value read
    have count : word after "peer.refcount" (address+nodeOffsets.peerRefcount) 4=
        word before "peer.refcount" (address+nodeOffsets.peerRefcount) 4 := by
      apply (Trie.word_frame same _ _ _ _).symm
      apply apart (address+nodeOffsets.peerRefcount,4)
      exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨(id,address),member,
          List.mem_map.mpr ⟨(nodeOffsets.peerRefcount,4),by simp [peerFields],rfl⟩⟩))
    have decoder : decodePeer n nodeOffsets after id address=decodePeer n nodeOffsets before id address := by
      simp only [decodePeer,count,metadata.heads id address member,metadata.lists id address member]
    rw [decoder]
    exact pending.peers (id,address) member value read
  · intro offset size within path
    apply Eq.trans (Trie.word_frame same path _ _ _).symm (pending.table offset size within path)
    intro a inside
    apply tableApart a
    obtain ⟨i,bound,equal⟩ := inside
    refine ⟨offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
  · intro id node member internal
    rw [←internalListCheck_frame n nodeOffsets same metadataApart id]
    exact pending.internal id node member internal

/-- Recover an old node's core from the original relation and the pending
resource, without asserting a new reconstruction while the fresh node is unpublished. -/
theorem Pending.old_node {names entry d key cidr pid base memory id address node}
    (pending : Pending names entry d key cidr pid base memory)
    (related : Corresponds names nodeOffsets entry.dmem d)
    (named : (id,address) ∈ names.trie.nodes) (present : d.nodes.get? id=some node) :
    Trie.decodeNode (names.allocated base).trie nodeOffsets memory address=.ok (Trie.targetNode node) := by
  obtain ⟨⟨current,actual⟩,member,read⟩ := (reconstruct_fields related).nodes.left (id,address) named
  have identity := (decodeNode_fields read).1
  dsimp only at identity
  subst current
  have found : d.nodes.get? id=some actual := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
  have equal : actual=node := Option.some.inj (found.symm.trans present)
  subst actual
  exact (decodeNode_fields (pending.nodes _ named _ read)).2

#print axioms Pending.frame
end Binary.Pair.Allowedips.NodeInit
