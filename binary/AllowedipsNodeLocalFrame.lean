import AllowedipsNodeBoundaryFields
import AllowedipsNodeInitFrame
import AllowedipsQueryFrame

namespace Binary.Pair.Allowedips.NodeInit
open Root

theorem writeSpans_cover (names : Names) (s : MachineData) (base : Nat) :
    Covers (writeSpans (names.allocated base) s base) (EntryWrites names s base) := by
  intro a inside
  rcases inside with fresh | list | stack
  · exact ⟨(base,72),by simp [writeSpans],fresh⟩
  · rcases list with ⟨link,slot,offset,which,inside⟩
    have within : InRange (.ofNat 64 link) 16 a := by
      obtain ⟨i,bound,equal⟩ := inside
      refine ⟨offset+i,by rcases which with rfl|rfl <;> omega,?_⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
    cases slot with
    | node named =>
      exact ⟨_,List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,named,rfl⟩)),within⟩
    | peer named =>
      exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨_,named,rfl⟩),within⟩
  · obtain ⟨offset,member,inside⟩ := stack
    refine ⟨(s.regs.rsp.toNat+offset,1),?_,inside⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> simp [writeSpans]

theorem BoundaryFields.query_extent {names o world machine key cidr pid base}
    (fields : BoundaryFields names o world machine key cidr pid base) :
    machine.data.regs.r13.toNat+machine.data.regs.rbp.toNat/8≤2^64 := by
  have all := List.all_eq_true.mp fields.queryApart _ (List.mem_singleton_self _)
  have checked := List.all_eq_true.mp all (base,72) (by simp [writeSpans])
  have bounds : (machine.data.regs.r13.toNat+machine.data.regs.rbp.toNat/8≤2^64 ∧ base+72≤2^64) ∧
      disjointRanges machine.data.regs.r13.toNat (machine.data.regs.rbp.toNat/8) base 72=true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using checked
  exact bounds.1.1

theorem BoundaryFields.query_separated {names o world machine key cidr pid base}
    (fields : BoundaryFields names o world machine key cidr pid base) :
    ∀ a, InRange machine.data.regs.r13.toBitVec (machine.data.regs.rbp.toNat/8) a →
      ¬EntryWrites names machine.data base a := by
  intro a read written
  obtain ⟨span,member,inside⟩ := writeSpans_cover names machine.data base a written
  exact spansApart_sound fields.queryApart (List.mem_singleton_self _) member
    (by simpa only [Span.contains,ofNat_uint64] using read) inside

theorem BoundaryFields.stack_node_apart {names o world machine key cidr pid base}
    (fields : BoundaryFields names o world machine key cidr pid base) :
    ∀ a, InRange (.ofNat 64 base) 72 a → ¬StackWrites machine.data.regs.rsp.toNat a := by
  intro a read ⟨offset,member,written⟩
  have atStack : (machine.data.regs.rsp.toNat+offset,1) ∈
      [(machine.data.regs.rsp.toNat+36,1),(machine.data.regs.rsp.toNat+43,1),
        (machine.data.regs.rsp.toNat+44,1)] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> simp
  exact spansApart_sound fields.stackApart (r:=(base,72)) atStack (by simp) written read

theorem BoundaryFields.zero_word {names world machine key cidr pid base}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (path : String) (offset size : Nat) (within : offset+size≤72) :
    word machine.data.dmem path (base+offset) size=.ok 0 := by
  have extent := (allocated_facts fields.allocated).2.2.1
  change base+72<2^64 at extent
  have part := MemoryBytes.loadInt_subword _ _ _ _ (Trie.readNat_loadInt fields.zero) offset size within
  apply Trie.word_of_loadInt _ (by omega)
  simpa [BitVec.ofNat_add] using part

theorem BoundaryFields.query_words {names o world machine key cidr pid base after}
    (fields : BoundaryFields names o world machine key cidr pid base)
    (frame : EqualOutside (EntryWrites names machine.data base) machine.data.dmem after) :
    if machine.data.regs.rbp.toNat=32 then word after "query" machine.data.regs.r13.toNat 4=.ok key else
      ∃ hi lo,word after "query.high" machine.data.regs.r13.toNat 8=.ok hi ∧
        word after "query.low" (machine.data.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo := by
  apply Placement.query_words_preserved fields.query fields.family fields.query_extent
  intro offset size within path
  apply (Trie.word_frame frame path _ _ _).symm
  intro a inside
  apply fields.query_separated a
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc,ofNat_uint64] using equal

end Binary.Pair.Allowedips.NodeInit
