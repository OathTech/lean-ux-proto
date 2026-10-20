import AllowedipsRootFrame
import AllowedipsAllocationValidate

namespace Binary.Pair.Allowedips.Root

/-- Table/allocation separation is available before the new allocation has a
valid record. Extract it from interpretation validation, not reconstruction. -/
theorem table_valid_geometry {names o} (valid : validate names o=.ok ()) :
    names.table+24<2^64 ∧ ∀ span ∈ allocations names o,
      disjointRanges span.1 span.2 names.table 24=true := by
  unfold validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨table,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,ranges,_⟩ := bind_ok valid
  have tableOriginal : (0<names.table ∧ names.table%8=0) ∧
      names.table+AllowedipsMutationLayout.tableSize<2^64 := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using table
  have tableFacts : (0<names.table ∧ names.table%8=0) ∧ names.table+24<2^64 := tableOriginal
  refine ⟨tableFacts.2,?_⟩
  exact forIn_ok (P:=fun span : Span => disjointRanges span.1 span.2 names.table 24=true)
    (fun span _ _ _ run => by
      obtain ⟨apart,run⟩ := check_ok _ _ _ _ run
      exact ⟨(),(Except.ok.inj run).symm,apart⟩) ranges

theorem table_allocation_bytes {names o span offset size field width}
    (valid : validate names o=.ok ()) (g : Geometry names o)
    (named : span ∈ allocations names o)
    (tableWithin : offset+size≤24) (allocationWithin : field+width≤span.2) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a →
      ¬InRange (.ofNat 64 (span.1+field)) width a := by
  have table := table_valid_geometry valid
  have extent := g.bounded span named
  have apart : span.1+span.2≤names.table ∨ names.table+24≤span.1 := by
    simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using table.2 span named
  intro a first second
  have := Span.location (span:=(names.table+offset,size)) (by omega) first
  have := Span.location (span:=(span.1+field,width)) (by omega) second
  rcases apart with left|right <;> omega

theorem table_lists_apart {names o offset size}
    (valid : validate names o=.ok ()) (g : Geometry names o) (layout : o.nodeSize=72)
    (within : offset+size≤24) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a → ¬ListWrites names a := by
  rintro a inside ⟨link,slot,field,which,written⟩
  cases slot with
  | node named =>
    exact table_allocation_bytes valid g (node_allocation named) within
      (field:=56+field) (width:=8) (by dsimp only; rw [layout]; rcases which with rfl|rfl <;> decide)
      a inside (by simpa only [Nat.add_assoc] using written)
  | peer named =>
    exact table_allocation_bytes valid g (peer_allocation named) within
      (field:=1096+field) (width:=8) (by dsimp only; rcases which with rfl|rfl <;> decide)
      a inside (by simpa only [Nat.add_assoc] using written)

theorem initialization_lists_apart {names o id base slotOffset}
    (valid : validate names o=.ok ()) (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,base) ∈ names.trie.nodes) (rootWithin : slotOffset+8≤24) :
    ∀ a, ListWrites names a → ¬InitWrites base (names.table+slotOffset) a := by
  intro a list written
  rcases written with record|root
  · exact node_before_list_apart g layout named (offset:=0) (size:=56) (by decide)
      a (by simpa only [Nat.add_zero] using record) list
  · exact table_lists_apart valid g layout rootWithin a root list

theorem peer_count_apart {names o pid peer id base slotOffset}
    (valid : validate names o=.ok ()) (g : Geometry names o) (layout : o.nodeSize=72)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (named : (id,base) ∈ names.trie.nodes)
    (rootWithin : slotOffset+8≤24) :
    ∀ a, InRange (.ofNat 64 (peer+Layouts.peer_refcount)) 4 a →
      ¬Writes names base (names.table+slotOffset) a := by
  intro a inside written
  rcases written with list|record|root
  · exact peer_count_list_apart g layout peerNamed a inside list
  · exact g.slices_apart (peer_allocation peerNamed) (node_allocation named)
      Layouts.peer_refcount 4 0 56 (by dsimp only; decide)
      (by dsimp only; rw [layout]; decide) (by
        intro equal
        have sizes := congrArg Prod.snd equal
        change Layouts.peerSize=o.nodeSize at sizes
        rw [layout] at sizes
        contradiction)
      a inside (by simpa only [Nat.add_zero] using record)
  · exact table_allocation_bytes valid g (peer_allocation peerNamed) rootWithin
      (field:=Layouts.peer_refcount) (width:=4) (by dsimp only; decide) a root inside

theorem table_field_apart {names o id base offset size slotOffset}
    (valid : validate names o=.ok ()) (g : Geometry names o) (layout : o.nodeSize=72)
    (named : (id,base) ∈ names.trie.nodes) (within : offset+size≤24)
    (rootWithin : slotOffset+8≤24)
    (different : offset+size≤slotOffset ∨ slotOffset+8≤offset) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a →
      ¬Writes names base (names.table+slotOffset) a := by
  intro a inside written
  rcases written with list|record|root
  · exact table_lists_apart valid g layout within a inside list
  · exact table_allocation_bytes valid g (node_allocation named) within
      (field:=0) (width:=56) (by dsimp only; rw [layout]; decide)
      a inside (by simpa only [Nat.add_zero] using record)
  · have apart := InRange.offset_disjoint (.ofNat 64 names.table)
      offset size slotOffset 8 (by omega) (by omega) different
    exact apart a (by simpa only [BitVec.ofNat_add] using inside)
      (by simpa only [BitVec.ofNat_add] using root)

#print axioms initialization_lists_apart
#print axioms peer_count_apart
#print axioms table_field_apart
end Binary.Pair.Allowedips.Root
