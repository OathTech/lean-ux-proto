import PairInsertEntryFacts
import PairCheckComplete

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

/-- Assemble the executable boundary check from present-state facts. This is
used for concrete witnesses and for caller installation over a retained heap. -/
theorem boundary_of_parts {n o c s w owner ra base}
    (asserted : Remove.assertAt n o s.data.dmem w=.ok ())
    (address : addressOf n owner=.ok base)
    (args : (s.pc.toBitVec.toNat==entry && s.data.regs.rdi.toNat==n.table && s.data.regs.rsi.toNat==base)=true)
    (resident : Resident n o s.data.dmem owner base)
    (facts : FrameFacts n o c s ra) (input : w.hidden.isSome=true) :
    callBoundary n o c s w owner ra=.ok () := by
  obtain ⟨next,nextRead⟩ := resident.next
  obtain ⟨index,indexRead⟩ := resident.index
  unfold callBoundary
  rw [asserted,address]
  apply check_of _ _ _ _ args
  rw [resident.kind]
  apply check_of
  · cases owner <;> rfl
  · rw [nextRead,indexRead,facts.toCallFacts.checked]
    apply check_of _ _ _ _ (Trie.coverageDataCheck_complete facts.nested)
    apply check_of _ _ _ _ (by simpa only [beq_iff_eq] using facts.nestedHardirq)
    split
    next needed =>
      apply check_of _ _ _ _ (by simp only [facts.nestedPending needed,beq_self_eq_true])
      apply check_of _ _ _ _ (facts.nestedApart needed)
      rfl
    next absent =>
      rfl

#print axioms boundary_of_parts
end Binary.Pair.Insert
