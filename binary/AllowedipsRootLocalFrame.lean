import AllowedipsRootBoundaryResources

namespace Binary.Pair.Allowedips.Root

theorem BoundaryFields.local_bounds {names o world machine key cidr pid}
    (fields : BoundaryFields names o world machine key cidr pid)
    (span : Span) (member : span ∈ [(machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8),
      (machine.data.regs.rsp.toNat+8,8),(machine.data.regs.rsp.toNat+16,4)]) : span.1+span.2≤2^64 := by
  have all := List.all_eq_true.mp fields.apart span member
  have checked := List.all_eq_true.mp all (machine.data.regs.rbx.toNat,72)
    (by simp [writeSpans])
  have bounds : (span.1+span.2≤2^64 ∧ machine.data.regs.rbx.toNat+72≤2^64) ∧
      disjointRanges span.1 span.2 machine.data.regs.rbx.toNat 72=true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using checked
  exact bounds.1.1

theorem BoundaryFields.local_word_frame {names o world machine key cidr pid after}
    (fields : BoundaryFields names o world machine key cidr pid)
    (frame : EqualOutside (EntryWrites names machine.data) machine.data.dmem after)
    (span : Span) (member : span ∈ [(machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8),
      (machine.data.regs.rsp.toNat+8,8),(machine.data.regs.rsp.toNat+16,4)])
    (offset size : Nat) (within : offset+size≤span.2) (path : String) :
    word after path (span.1+offset) size=word machine.data.dmem path (span.1+offset) size := by
  apply (Trie.word_frame frame path _ _ _).symm
  intro a inside
  apply fields.separated span member a
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

theorem BoundaryFields.saved_word {names o world machine key cidr pid after}
    (fields : BoundaryFields names o world machine key cidr pid)
    (frame : EqualOutside (EntryWrites names machine.data) machine.data.dmem after) :
    word after "root.slot" (machine.data.regs.rsp.toNat+8) 8=
      .ok (names.table+(if machine.data.regs.rbp.toNat=32 then 0 else 8)) := by
  have kept := fields.local_word_frame frame (machine.data.regs.rsp.toNat+8,8) (by simp)
    0 8 (by simp) "root.slot"
  simp only [Nat.add_zero] at kept
  rw [kept]
  exact Trie.word_of_loadInt _ (fields.local_bounds (machine.data.regs.rsp.toNat+8,8) (by simp)) (Trie.readNat_loadInt fields.saved)

theorem BoundaryFields.cidr_word {names o world machine key cidr pid after}
    (fields : BoundaryFields names o world machine key cidr pid)
    (frame : EqualOutside (EntryWrites names machine.data) machine.data.dmem after) :
    word after "root.cidr" (machine.data.regs.rsp.toNat+16) 4=.ok cidr := by
  have kept := fields.local_word_frame frame (machine.data.regs.rsp.toNat+16,4) (by simp)
    0 4 (by simp) "root.cidr"
  simp only [Nat.add_zero] at kept
  rw [kept]
  exact Trie.word_of_loadInt _ (fields.local_bounds (machine.data.regs.rsp.toNat+16,4) (by simp)) (Trie.readNat_loadInt fields.cidrRead)

theorem BoundaryFields.query_words {names o world machine key cidr pid after}
    (fields : BoundaryFields names o world machine key cidr pid)
    (frame : EqualOutside (EntryWrites names machine.data) machine.data.dmem after) :
    if machine.data.regs.rbp.toNat=32 then word after "query" machine.data.regs.r13.toNat 4=.ok key else
      ∃ hi lo,word after "query.high" machine.data.regs.r13.toNat 8=.ok hi ∧
        word after "query.low" (machine.data.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo := by
  have input := Placement.queryLocals_fields fields.query
  have extent := fields.local_bounds (machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8) (by simp)
  have keep := fields.local_word_frame frame (machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8) (by simp)
  have address : BitVec.ofNat 64 machine.data.regs.r13.toNat=machine.data.regs.r13.toBitVec :=
    ofNat_uint64 _
  rcases fields.family with four|six
  · rw [ite_eq_left four]
    have first := keep 0 4 (by simp [four]) "query"
    simp only [Nat.add_zero] at first
    rw [first]
    apply Trie.word_of_loadInt _ (by simpa only [four,Nat.reduceDiv] using extent)
    simpa only [AllowedipsChild.QueryWords,four,ite_true,address] using input
  · have not4 : machine.data.regs.rbp.toNat≠32 := by omega
    rw [ite_eq_right not4]
    have input : machine.data.dmem.loadInt machine.data.regs.r13.toBitVec 8=some ((key/2^64 : Nat) : Int) ∧
        machine.data.dmem.loadInt (machine.data.regs.r13.toBitVec+8) 8=some ((key%2^64 : Nat) : Int) := by
      simpa only [AllowedipsChild.QueryWords,ite_eq_right not4] using input
    have extent : machine.data.regs.r13.toNat+16≤2^64 := by simpa only [six,Nat.reduceDiv] using extent
    refine ⟨key/2^64,key%2^64,?_,?_,by omega⟩
    · have first := keep 0 8 (by simp [six]) "query.high"
      simp only [Nat.add_zero] at first
      rw [first]
      apply Trie.word_of_loadInt _ (by omega)
      simpa only [address] using input.1
    · rw [keep 8 8 (by simp [six]) "query.low"]
      apply Trie.word_of_loadInt _ (by omega)
      simpa only [BitVec.ofNat_add,address,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl] using input.2

#print axioms BoundaryFields.query_words
end Binary.Pair.Allowedips.Root
