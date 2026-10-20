import AllowedipsOwnerUpdate

namespace Binary.Pair.Allowedips

theorem table_geometry {names o m d} (related : Corresponds names o m d) :
    names.table+24<2^64 ∧ ∀ span ∈ allocations names o,
      disjointRanges span.1 span.2 names.table 24=true := by
  have valid := (reconstruct_fields related).valid
  unfold validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨table,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,ranges,_⟩ := bind_ok valid
  have tableFacts : (0<names.table ∧ names.table%8=0) ∧ names.table+AllowedipsMutationLayout.tableSize<2^64 := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using table
  refine ⟨tableFacts.2,?_⟩
  exact forIn_ok (P := fun span : Span => disjointRanges span.1 span.2 names.table 24=true)
    (fun span _ _ _ run => by
      obtain ⟨apart,run⟩ := check_ok _ _ _ _ run
      exact ⟨(),(Except.ok.inj run).symm,apart⟩) ranges

theorem table_allocation_apart {names o m d span offset size field width}
    (related : Corresponds names o m d) (named : span ∈ allocations names o)
    (tableWithin : offset+size≤24) (writeWithin : field+width≤span.2) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a →
      ¬InRange (.ofNat 64 (span.1+field)) width a := by
  have table := table_geometry related
  have spanBound := (geometry related).bounded span named
  have ranges : span.1+span.2≤names.table ∨ names.table+24≤span.1 := by
    simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using table.2 span named
  intro a read write
  have := Span.location (span:=(names.table+offset,size)) (by omega) read
  have := Span.location (span:=(span.1+field,width)) (by omega) write
  rcases ranges with left|right <;> omega

theorem table_list_apart {names o m d offset size}
    (related : Corresponds names o m d) (within : offset+size≤24) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a → ¬ListWrites names a := by
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  rintro a read ⟨link,slot,field,which,write⟩
  cases slot with
  | node named =>
    exact table_allocation_apart related (node_allocation named) within
      (field:=56+field) (width:=8) (by dsimp only; rw [layout]; rcases which with rfl|rfl <;> decide)
      a read (by simpa only [Nat.add_assoc] using write)
  | peer named =>
    exact table_allocation_apart related (peer_allocation named) within
      (field:=1096+field) (width:=8) (by dsimp only; rcases which with rfl|rfl <;> decide)
      a read (by simpa only [Nat.add_assoc] using write)

theorem table_owner_frame {names o entry m d id base offset size value}
    (related : Corresponds names o entry d) (named : (id,base) ∈ names.trie.nodes)
    (within : offset+size≤24) (path : String) :
    word (write64 m base value) path (names.table+offset) size=word m path (names.table+offset) size := by
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  apply word_write64_frame
  have apart := table_allocation_apart related (node_allocation named) within
    (field:=0) (width:=8) (by dsimp only; rw [layout]; decide)
  simpa only [Nat.add_zero] using apart

#print axioms table_geometry
end Binary.Pair.Allowedips
