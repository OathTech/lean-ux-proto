import Leanux.Proofs.WG.Progress.SeccompLocalFiniteSource

/-! The standalone Local interpreter has its own pure result/state boundary.
No product World or Kernel state is reconstructed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompLocalFinite
open Leanux Leanux.Seccomp

/-- All original Local outcomes agree with finite evaluation. On normal return
this includes the translated/error result and exact final steps, allocation
answers, failure-site list and remaining records. A Local Stop carries no final
state here, exactly as in the original interpreter. No successful conversion,
empty record suffix, install or prefill execution is assumed or concluded. -/
theorem original_convert_result_finite (prog : Seccomp.ClassicProg)
    (newProg : Option Nat) (seen : Bool) (newLen : Nat) (initial : Local.LState) :
    Local.run (bpfConvertFilter prog newProg seen newLen : Local.L _) initial =
      Local.run (convert prog newProg seen newLen) initial := by
  rw [convert_source]

end Leanux.Proofs.WG.Progress.SeccompLocalFinite
