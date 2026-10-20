import AllowedipsLoopInput

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation

theorem input_keyBytes (s : MachineData) (bits stored query : Nat)
    (family : bits = 32 ∨ bits = 128) (storedBound : stored < 2^bits) (queryBound : query < 2^bits)
    (a : BitVec 64) (read : CommonBits.ReadBytes (input s bits stored query).keyWords a) :
    KeyReads (s.regs.rdi.toBitVec+32) bits stored query a ∨
      InRange s.regs.rsi.toBitVec (bits/8) a := by
  obtain ⟨word,member,inside⟩ := read
  rcases family with rfl | rfl
  · rw [input_keyWords32 s stored query storedBound queryBound] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inl inside
    · exact .inr inside
  · rw [input_keyWords128 s stored query storedBound queryBound] at member
    rcases List.mem_append.mp member with high | low
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at high
      rcases high with rfl | rfl
      · exact .inl (.inl inside)
      · obtain ⟨n,bound,address⟩ := inside
        change n < 8 at bound
        exact .inr ⟨n,by omega,address⟩
    · split at low
      next equal =>
        simp only [List.mem_cons,List.not_mem_nil,or_false] at low
        rcases low with rfl | rfl
        · left
          right
          refine ⟨equal,?_⟩
          simpa only [BitVec.add_assoc,show (32+8 : BitVec 64)=40 from rfl] using inside
        · obtain ⟨n,bound,address⟩ := inside
          change n < 8 at bound
          right
          refine ⟨8+n,by omega,?_⟩
          simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl,BitVec.add_assoc] using address
      next different => cases low

/-- The helper's physical entry obligations follow from the current loop
frame and precisely the conditional node/query reads. -/
theorem input_caller (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (bits stored query : Nat) (family : bits = 32 ∨ bits = 128)
    (frame : Frame base coverage s)
    (familyByte : s.regs.get (.low .rdx .W8) = .ofNat 8 bits)
    (keyFields : KeyFields s.dmem (s.regs.rdi.toBitVec+32) bits stored query)
    (queryWords : AllowedipsChild.QueryWords s.dmem s.regs.rsi.toBitVec bits query)
    (keyApart : ∀ a, KeyReads (s.regs.rdi.toBitVec+32) bits stored query a → ¬writes base.regs.rsp coverage a)
    (queryApart : ∀ a, InRange s.regs.rsi.toBitVec (bits/8) a → ¬writes base.regs.rsp coverage a) :
    CommonBits.CallerAt (input s bits stored query) coverage s := by
  refine ⟨rfl,rfl,rfl,familyByte.symm,rfl,rfl,rfl,rfl,rfl,
    input_keys s bits stored query family keyFields queryWords,?_,frame.ready.state,
    frame.ready.aligned,?_,?_,frame.ready.metadataSeparate,frame.ready.preemptSeparate⟩
  · intro a read written
    have subset := input_keyBytes s bits stored query family keyFields.1 keyFields.2.1 a read
    have written' : writes base.regs.rsp coverage a := by
      simpa only [writes,CommonBits.CallerScratch,frame.stack] using written
    rcases subset with key | query
    · exact keyApart a key written'
    · exact queryApart a query written'
  · simpa only [frame.stack] using frame.mapped
  · simpa only [CommonBits.CallerScratch,frame.stack] using frame.coverageSeparate

#print axioms input_keyBytes
#print axioms input_caller
end Binary.AllowedipsLoop
