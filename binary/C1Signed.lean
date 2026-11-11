import C1Joined
import C1Referenced
import C1Witness

/-! Result C1: the compiled allowed-IPs insertion. `signed : Signed`, with no
hypothesis: the final statement of `StatementC1Vacuity` (the headline, the
witness and the two exclusions). `C1Joined` derives it from the packages'
theorems and two further propositions; `C1Referenced` and `C1Witness` prove
those. The report is `docs/2026-11-11-c1-allowedips-insertion.md`. -/
namespace Binary.Statements.C1.Proof
open Binary.Statements.C1

example : ReferencedHolds := referencedHolds
example : WitnessHolds := witnessHolds

/-- RESULT C1. -/
theorem signed : Signed := signed_of_referenced_and_witness referencedHolds witnessHolds

#print axioms signed
end Binary.Statements.C1.Proof
