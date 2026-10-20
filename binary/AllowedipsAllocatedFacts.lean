import AllowedipsRootMetadata

namespace Binary.Pair.Allowedips

theorem trie_validate_ranges {names : Trie.Names} {o : AllowedipsProbe.Offsets}
    (valid : Trie.validate names o=.ok ()) :
    ∀ span ∈ names.nodes.map (fun pair => (pair.2,o.nodeSize))++
      names.peers.map (fun pair => (pair.2,Layouts.peerSize)),
      0<span.1 ∧ span.1+span.2<2^64 := by
  unfold Trie.validate at valid
  obtain ⟨_,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,ranges,_⟩ := bind_ok valid
  have bounded := forIn_ok (P:=fun entry : Span×Nat => 0<entry.1.1 ∧ entry.1.1+entry.1.2<2^64)
    (fun entry _ _ _ run => by
      obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
      obtain ⟨_,_,run⟩ := bind_ok run
      exact ⟨(),(Except.ok.inj run).symm,by simpa using checked⟩) ranges
  intro span member
  obtain ⟨i,atIndex⟩ := List.mem_iff_getElem?.mp member
  exact bounded (span,i) (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)

/-- Invert the same extended-name validation that the runtime boundary uses.
No decoded fresh node is needed to recover allocator geometry. -/
theorem allocated_facts {names : Names} {o : AllowedipsProbe.Offsets} {address : Nat}
    (valid : validate (names.allocated address) o=.ok ()) :
    0<address ∧ address%8=0 ∧ address+o.nodeSize<2^64 ∧
    (∀ span ∈ allocations names o, disjointRanges address o.nodeSize span.1 span.2=true) ∧
    disjointRanges address o.nodeSize names.table 24=true := by
  have original := valid
  unfold validate at valid
  obtain ⟨_,trieValid,valid⟩ := bind_ok valid
  obtain ⟨_,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,aligns,_⟩ := bind_ok valid
  have aligned := forIn_ok (P:=fun pair : Nat×Nat => pair.2%8=0)
    (fun pair _ _ _ run => by
      obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
      exact ⟨(),(Except.ok.inj run).symm,by simpa using checked⟩) aligns
  have named := allocated_node names address
  have range := trie_validate_ranges trieValid (address,o.nodeSize) (node_allocation named)
  have pairs := Trie.validate_pairwise trieValid
  simp only [Names.allocated,List.map_append,List.map_cons,List.map_nil,List.pairwise_append] at pairs
  refine ⟨range.1,aligned _ named,range.2,?_,?_⟩
  · intro span member
    rcases List.mem_append.mp member with node | peer
    · have apart := pairs.1.2.2 span node (address,o.nodeSize) (List.mem_singleton_self _)
      simpa only [disjointRanges,Bool.or_comm] using apart
    · exact pairs.2.2 (address,o.nodeSize) (List.mem_append_right _ (List.mem_singleton_self _)) span peer
  · exact (Root.table_valid_geometry original).2 (address,o.nodeSize) (node_allocation named)

#print axioms allocated_facts
end Binary.Pair.Allowedips
