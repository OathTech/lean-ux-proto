import PairAllowedipsChildResources
import AllowedipsChildInitialized

namespace Binary.Pair.Allowedips.ChildResources
open Root ChildFinish CommonBitsCoverage

private theorem callback_cover (s : MachineData) (c : Context) :
    Covers (callbackSpans s c) (CallWrites s.regs.rsp c) := by
  intro a written
  rcases written with stack|covered
  · exact ⟨_,List.mem_append_left _ (List.mem_singleton_self _),by
      simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using stack⟩
  · obtain ⟨span,member,inside⟩ := Trie.writeSpans_cover covered
    exact ⟨span,List.mem_append_right _ member,inside⟩

private theorem setup_cover (s : MachineData) (c : Context) :
    Covers (setupSpans s c) (SetupWrites s.regs.rsp c) := by
  intro a written
  rcases written with stack|call
  · exact ⟨_,List.mem_append_left _ (List.mem_singleton_self _),by
      simpa only [Span.contains,ofNat_uint64,ChildSetup.Writes] using stack⟩
  · obtain ⟨span,member,inside⟩ := callback_cover s c a call
    exact ⟨span,List.mem_append_right _ member,inside⟩

private theorem publish_cover (s : MachineData) (base direction : Nat) (bit : direction<2) :
    Covers (publishSpans s base) (PublishWrites s.regs.rbx base direction) := by
  intro a written
  rcases written with parent|child
  · exact ⟨(base+48,8),by simp [publishSpans],parent⟩
  · refine ⟨(s.regs.rbx.toNat+8,16),by simp [publishSpans],?_⟩
    obtain ⟨i,bound,location⟩ := child
    refine ⟨direction*8+i,by omega,?_⟩
    simp only [←BitVec.ofNat_add] at location ⊢
    have sum : s.regs.rbx.toNat+direction*8+8+i=s.regs.rbx.toNat+8+(direction*8+i) := by omega
    simpa only [sum] using location

/-- All caller resources extracted from the checks exercised by the paired
runner. These are current-state facts, not assumptions about execution. -/
structure Ready (names : Names) (c : Context) (s : MachineData) (base : Nat) : Prop where
  extent : s.regs.rsp.toNat+32≤2^64
  mapped : ∀ offset size, offset+size≤32 →
    (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+offset)) size).isSome=true
  calls : CallsReady c s
  initialContext : ∀ a, c.bytes a → ¬NodeInit.EntryWrites names s base a
  setupContext : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a
  publishContext : ∀ direction<2, ∀ a, c.bytes a → ¬PublishWrites s.regs.rbx base direction a
  saved : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a
  projection : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
    ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a
  table : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a
  query : ∀ a, InRange s.regs.r13.toBitVec (s.regs.rbp.toNat/8) a → ¬SetupWrites s.regs.rsp c a
  destinations : ∀ direction<2, ∀ a, PublishWrites s.regs.rbx base direction a → ¬CallWrites s.regs.rsp c a
  index : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a → ¬InRange (.ofNat 64 (base+48)) 8 a

theorem resources_ready {names c s base}
    (checked : resources names nodeOffsets c s base=.ok ()) : Ready names c s base := by
  unfold resources at checked
  obtain ⟨extent,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨mapped,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨calls,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨contextApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨savedApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨readApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨destinationsApart,checked⟩ := require_bind_ok _ _ _ _ checked
  have indexApart := require_ok checked
  have contextCover : Covers (Trie.readSpans c) c.bytes := fun _ read => Trie.readSpans_cover read
  have contextSeparated {Q : BitVec 64 → Prop}
      (cover : Covers (NodeInit.writeSpans (names.allocated base) s base++
        [(s.regs.rsp.toNat,32)]++publishSpans s base) Q) :=
    spansApart_disjoint contextApart contextCover cover
  have setupSeparated {P : BitVec 64 → Prop}
      (cover : Covers (readSpans (names.allocated base) nodeOffsets++
        [(names.table,24),(s.regs.r13.toNat,s.regs.rbp.toNat/8)]) P) :=
    spansApart_disjoint readApart cover (setup_cover s c)
  refine ⟨of_decide_eq_true extent,?_,(Trie.frameCheck_sound calls).ready,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro offset size within
    obtain ⟨value,read⟩ := Option.isSome_iff_exists.mp mapped
    have subword := MemoryBytes.loadInt_subword _ _ _ _ read offset size within
    have mapped := Option.isSome_of_eq_some subword
    simpa only [BitVec.ofNat_add,ofNat_uint64] using mapped
  · exact contextSeparated ((NodeInit.writeSpans_cover names s base).append_left.append_left)
  · have cover : Covers [(s.regs.rsp.toNat,32)] (ChildSetup.Writes s.regs.rsp) := Covers.range _ _
    exact contextSeparated cover.append_right.append_left
  · intro direction bit
    exact contextSeparated (publish_cover s base direction bit).append_right
  · exact spansApart_disjoint savedApart (Covers.range _ _) (callback_cover s c)
  · intro span member
    apply setupSeparated
    intro a inside
    exact ⟨span,List.mem_append_left _ member,inside⟩
  · apply setupSeparated
    intro a inside
    exact ⟨(names.table,24),List.mem_append_right _ (by simp),inside⟩
  · apply setupSeparated
    intro a inside
    exact ⟨(s.regs.r13.toNat,s.regs.rbp.toNat/8),List.mem_append_right _ (by simp),by
      simpa only [Span.contains,ofNat_uint64] using inside⟩
  · intro direction bit
    exact spansApart_disjoint destinationsApart (publish_cover s base direction bit) (callback_cover s c)
  · exact fun _ h => spansApart_sound indexApart (l:=(s.regs.rsp.toNat+16,8)) (r:=(base+48,8)) (by simp) (by simp) h

#print axioms resources_ready
end Binary.Pair.Allowedips.ChildResources
