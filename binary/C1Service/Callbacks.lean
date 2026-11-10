import C1Interfaces
import C1Service.CallbackCmp1

/-! Result C1, work package 4: the two comparison callbacks in the form of the
interface (`CallbacksFromImage`). Everything that depends on that form is
here; the proofs are in `C1Service.CallbackCmp1` and `C1Service.CallbackCmp8`,
which do not depend on result C1's statements beyond its image terms. -/
namespace Binary.Statements.C1.Proof
open Binary.TrustBase Binary.Statements.C1

/-- ACCEPTANCE: `__sanitizer_cov_trace_cmp1` from the image's terms. -/
theorem cmp1FromImage : Cmp1FromImage :=
  fun fetch image => Callback.Cmp1.cmp1_contract fetch image.1 image.2

#print axioms cmp1FromImage
end Binary.Statements.C1.Proof
