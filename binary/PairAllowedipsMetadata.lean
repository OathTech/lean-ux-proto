import PairAllowedipsCount

namespace Binary.Pair.Allowedips

theorem MetadataSame.of_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (names : Names) (o : AllowedipsProbe.Offsets)
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ metadataSpans names o, ∀ a, span.contains a → ¬writes a) :
    MetadataSame names o before after := by
  have wordSame (base size : Nat) (member : (base,size) ∈ metadataSpans names o) (path : String) :
      word before path base size=word after path base size :=
    Trie.word_frame same path base size (apart _ member)
  have tableRead (offset size : Nat) (field : (offset,size) ∈ tableFields) (path : String) :=
    wordSame (names.table+offset) size
      (List.mem_append_left _ (List.mem_map.mpr ⟨(offset,size),field,rfl⟩)) path
  have nodeRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.nodes)
      (field : (offset,size) ∈ nodeFields o) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  have peerRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.peers)
      (field : (offset,size) ∈ listFields) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  have nodeLists (id a : Nat) (named : (id,a) ∈ names.trie.nodes) (path : String)
      (offset : Nat) (which : offset=0 ∨ offset=8) :
      word before path (a+AllowedipsMutationLayout.peer_list+offset) 8=
        word after path (a+AllowedipsMutationLayout.peer_list+offset) 8 := by
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using nodeRead id a AllowedipsMutationLayout.peer_list 8 named
        (by simp [nodeFields]) path
    · simpa only [Nat.add_assoc] using nodeRead id a (AllowedipsMutationLayout.peer_list+8) 8 named
        (by simp [nodeFields]) path
  have heads (id a : Nat) (named : (id,a) ∈ names.trie.peers) (path : String)
      (offset : Nat) (which : offset=0 ∨ offset=8) :
      word before path (a+AllowedipsMutationLayout.allowedips_list+offset) 8=
        word after path (a+AllowedipsMutationLayout.allowedips_list+offset) 8 := by
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using peerRead id a AllowedipsMutationLayout.allowedips_list 8 named
        (by simp [listFields]) path
    · simpa only [Nat.add_assoc] using peerRead id a (AllowedipsMutationLayout.allowedips_list+8) 8 named
        (by simp [listFields]) path
  refine ⟨?_,?_,?_,?_⟩
  · intro offset field path
    apply (tableRead offset 8 _ path).symm
    simpa [tableFields] using field
  · intro id a named
    have core : Trie.decodeNode names.trie o before a=Trie.decodeNode names.trie o after a := by
      apply Trie.decodeNode_congr
      intro offset size field path
      exact nodeRead id a offset size named (List.mem_append_left _ field) path
    have parent := nodeRead id a AllowedipsMutationLayout.parent_bit_packed 8 named
      (by simp [nodeFields]) "node.parent"
    simp only [decodeNode,core,parent]
  · intro id a named
    simpa only [Nat.add_zero] using (heads id a named "peer.list.head" 0 (Or.inl rfl)).symm
  · intro id a named first
    exact (peerList_congr names before after _ (heads id a named) nodeLists _ first _ []).symm

#print axioms MetadataSame.of_frame
end Binary.Pair.Allowedips
