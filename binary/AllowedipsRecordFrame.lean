import AllowedipsDecodeConstruct

namespace Binary.Pair.Allowedips

theorem node_field_bounds {names o m d offset size}
    (related : Corresponds names o m d) (field : (offset,size) ∈ Trie.nodeSpans o) :
    offset+size≤56 ∧ (offset=o.peer ∨ 8≤offset) := by
  have layout := (Trie.reconstruct_fields related.trie).layout
  rcases layout with ⟨_,peer,children,cidr,byte,bit,width,key,_⟩
  simp only [Trie.nodeSpans,peer,children,cidr,byte,bit,width,key,
    AllowedipsLayout.peer,AllowedipsLayout.bit,AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,
    AllowedipsLayout.bit_at_b,AllowedipsLayout.bitlen,AllowedipsLayout.bits,
    List.mem_cons,List.not_mem_nil,or_false] at field
  rw [peer]
  rcases field with h|h|h|h|h|h|h|h|h|h
  all_goals rcases Prod.mk.inj h with ⟨rfl,rfl⟩; decide

/-- Record bytes survive list writes even after a separately-proved owner
word change. Geometry comes from the original entry; it is memory-independent. -/
theorem node_record_list_frame_from {names o entry before after d id base}
    (related : Corresponds names o entry d) (named : (id,base) ∈ names.trie.nodes)
    (frame : EqualOutside (ListWrites names) before after) :
    decodeNode names o after id base=decodeNode names o before id base := by
  have g := geometry related
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  have core : Trie.decodeNode names.trie o after base=Trie.decodeNode names.trie o before base := by
    apply Trie.decodeNode_congr
    intro offset size field path
    exact (Trie.word_frame frame path (base+offset) size
      (node_before_list_apart g layout named (node_field_bounds related field).1)).symm
  have parent := Trie.word_frame frame "node.parent" (base+AllowedipsMutationLayout.parent_bit_packed) 8
    (node_before_list_apart g layout named (by decide))
  simp only [decodeNode,core,←parent]

theorem node_owner_frame {names o entry m d id base focusId focus offset size value}
    (related : Corresponds names o entry d) (named : (id,base) ∈ names.trie.nodes)
    (focusNamed : (focusId,focus) ∈ names.trie.nodes) (within : offset+size≤56)
    (unchanged : id≠focusId ∨ 8≤offset) (path : String) :
    word (write64 m focus value) path (base+offset) size=word m path (base+offset) size := by
  have core := Trie.reconstruct_fields related.trie
  have layout : o.nodeSize=72 := core.layout.1
  apply word_write64_frame
  have apart := (geometry related).slices_apart (node_allocation named) (node_allocation focusNamed)
    offset size 0 8 (by dsimp only; rw [layout]; omega) (by dsimp only; rw [layout]; decide) (by
      intro equal
      rcases unchanged with different|later
      · have bases := congrArg Prod.fst equal
        dsimp only at bases
        have first := find_address (name_addresses related).1 named
        have second := find_address (name_addresses related).1 focusNamed
        rw [bases] at first
        exact False.elim (different (congrArg Prod.fst (Option.some.inj (first.symm.trans second))))
      · exact .inr later)
  simpa only [Nat.add_zero] using apart

theorem peer_owner_frame {names o entry m d id base focusId focus value}
    (related : Corresponds names o entry d) (named : (id,base) ∈ names.trie.peers)
    (focusNamed : (focusId,focus) ∈ names.trie.nodes) (path : String) :
    word (write64 m focus value) path (base+o.peerRefcount) 4=word m path (base+o.peerRefcount) 4 := by
  have core := Trie.reconstruct_fields related.trie
  have layout : o.nodeSize=72 := core.layout.1
  have count : o.peerRefcount=Layouts.peer_refcount := core.layout.2.2.2.2.2.2.2.2
  apply word_write64_frame
  have apart := (geometry related).slices_apart (peer_allocation named) (node_allocation focusNamed)
    o.peerRefcount 4 0 8 (by dsimp only; rw [count]; decide) (by dsimp only; rw [layout]; decide)
    (fun _ => .inr (by rw [count]; decide))
  simpa only [Nat.add_zero] using apart

#print axioms node_record_list_frame_from
end Binary.Pair.Allowedips
