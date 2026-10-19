import Leanux.Proofs.WG.Progress.SeccompFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompFinite
open Leanux Leanux.Seccomp
/-- Campaign projection of the concrete native converter. This includes failure
outcomes, and is not a claim about its surrounding install/prefill callers. -/
theorem original_convert_finite (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seen : Bool) (newLen : Nat) :
    Campaign2.Product.AgreesOn (fun _=>True)
      (liftSeccomp (bpfConvertFilter prog newProg seen newLen))
      (liftSeccomp (convert prog newProg seen newLen)) := by
  rw [convert_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.SeccompFinite
