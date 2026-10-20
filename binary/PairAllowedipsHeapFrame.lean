import PairAllowedipsLookupFrame

namespace Binary.Pair.Allowedips

theorem heap_mapCounts (names : Names) (state : State) (memory : DataMem) (f : Nat → Nat → Nat) :
    heap names (mapCounts f state) memory=heap names state memory := by
  simp only [heap,mapCounts,Trie.heap,List.flatMap_map]
  rfl

theorem internalListCheck_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (names : Names) (o : AllowedipsProbe.Offsets) (same : EqualOutside writes before after)
    (apart : ∀ span ∈ metadataSpans names o, ∀ a, span.contains a → ¬writes a) (id : Nat) :
    internalListCheck names before id=internalListCheck names after id := by
  simp only [internalListCheck,Trie.address]
  cases found : names.trie.nodes.find? (·.1 == id) with
  | none => rfl
  | some pair =>
    rcases pair with ⟨pid,a⟩
    dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
    have named := List.mem_of_find?_eq_some found
    have read (offset : Nat) (field : (offset,8) ∈ nodeFields o) :
        readNat ⟨{dmem := before},0⟩ (a+offset) 8=
          readNat ⟨{dmem := after},0⟩ (a+offset) 8 := by
      have member : (a+offset,8) ∈ metadataSpans names o :=
        List.mem_append_right _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨(pid,a),named,List.mem_map.mpr ⟨(offset,8),field,rfl⟩⟩))
      have bytes := same.loadBytes (.ofNat 64 (a+offset)) 8 (by
        intro i hi
        exact apart _ member _ ⟨i,hi,rfl⟩)
      simp only [readNat,bytes]
    simp only [read AllowedipsMutationLayout.peer_list (by simp [nodeFields])]
    have next := read (AllowedipsMutationLayout.peer_list+8) (by simp [nodeFields])
    have next' : readNat ⟨{dmem := before},0⟩ (a+AllowedipsMutationLayout.peer_list+8) 8=
        readNat ⟨{dmem := after},0⟩ (a+AllowedipsMutationLayout.peer_list+8) 8 := by
      simpa only [Nat.add_assoc] using next
    rw [next']

theorem heap_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (names : Names) (o : AllowedipsProbe.Offsets) (state : State)
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ metadataSpans names o, ∀ a, span.contains a → ¬writes a) :
    heap names state before=heap names state after := by
  have checks : internalListCheck names before=internalListCheck names after :=
    funext (internalListCheck_frame names o same apart)
  simp only [heap,checks]

#print axioms heap_mapCounts
#print axioms heap_frame
end Binary.Pair.Allowedips
