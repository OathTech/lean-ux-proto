import PairAllocationProof

namespace Binary.Pair.Trie
open Leanux Leanux.WG

/-- One scalar heap mutation plus an arbitrary disjoint scratch/service
footprint. Allocation separation comes from the executable decoder's own
validation; the caller supplies no per-peer unchanged-value equations. -/
theorem reconstruct_peer_frame {names o before after d id peer} {count base : Nat}
    (related : Corresponds names o before d) (present : d.peers.get? id = some peer)
    (named : (id,base) ∈ names.peers) (scratch : BitVec 64 → Prop)
    (frame : EqualOutside (fun a => InRange (.ofNat 64 (base+o.peerRefcount)) 4 a ∨ scratch a) before after)
    (scratchApart : ∀ a, ReadBytes names o a → ¬scratch a)
    (nodeApart : ∀ a, NodeReadBytes names o a → ¬InRange (.ofNat 64 (base+o.peerRefcount)) 4 a)
    (changed : after.loadInt (.ofNat 64 (base+o.peerRefcount)) 4 = some (count : Int)) :
    Corresponds names o after {d with peers := d.peers.insert id {peer with refcount := count}} := by
  apply reconstruct_peer_update related present
  · intro node address member
    symm
    apply decodeNode_congr
    intro offset size field path
    apply word_frame frame path
    intro a inside written
    have read : NodeReadBytes names o a := ⟨node,address,member,offset,size,field,inside⟩
    rcases written with countWord | extra
    · exact nodeApart a read countWord
    · exact scratchApart a (.inl read) extra
  · intro otherBase otherNamed
    have unique := (reconstruct_fields related).peerIds
    have same : (id,otherBase) = (id,base) :=
      Option.some.inj ((find_identity unique otherNamed).symm.trans (find_identity unique named))
    have sameBase := congrArg Prod.snd same
    dsimp only at sameBase
    subst otherBase
    exact changed
  · intro other otherBase otherNamed different
    symm
    apply word_frame frame
    intro a inside written
    rcases written with countWord | extra
    · exact other_count_separate related otherNamed named different a inside countWord
    · exact scratchApart a (.inr ⟨other,otherBase,otherNamed,inside⟩) extra

#print axioms reconstruct_peer_frame
end Binary.Pair.Trie
