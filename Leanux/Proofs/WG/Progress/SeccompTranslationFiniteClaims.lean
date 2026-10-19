import Leanux.Proofs.WG.Progress.SeccompTranslationFiniteSource

/-! The executable check has its own pure result boundary. This equality
retains rejected errno, Local Stop and both engines' results; it does not assert
that those results agree, nor that a program is accepted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompTranslationFinite
open Leanux Leanux.Seccomp

theorem original_check_result_finite (p : Seccomp.ClassicProg) (d : Seccomp.SeccompData) :
    checkTranslation p d = check p d :=
  check_source p d

end Leanux.Proofs.WG.Progress.SeccompTranslationFinite
