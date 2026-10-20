import PairInsertProvider
import PairCheckComplete

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage

/-- Reassemble the executable check from the same present-state fields.
No later execution or source outcome is part of these facts. -/
theorem ProviderFacts.checked {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) :
    providerCheck n o c initial ra config=.ok () := by
  unfold providerCheck
  rw [facts.wide.checked]
  apply check_of
  · simp only [facts.privilege,facts.direction,beq_self_eq_true,Bool.not_false,Bool.and_self]
  · apply check_of
    · by_cases needed : (Context.mk c.coverage (c.preempt+512)).Needed
      · simp only [needed,decide_true,Bool.not_true,Bool.false_or,decide_eq_true_eq]
        exact facts.capacity needed
      · simp only [needed,decide_false,Bool.not_false,Bool.true_or]
    · rw [facts.privateCheck]
      apply check_of _ _ _ _ facts.privateApart
      apply check_of _ _ _ _ facts.pendingApart
      rfl

#print axioms ProviderFacts.checked
end Binary.Pair.Insert
