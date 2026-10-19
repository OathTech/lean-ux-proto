import Leanux.Proofs.WG.Progress.SeccompFilterFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Preparation only: these all-outcome claims do not establish completion of
set-mode attachment, installation, prefill or Runner. Native source equality
also retains exact filter/task stores, which the WG campaign view omits. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompFilterFinite
open Leanux Leanux.Seccomp

theorem original_prepare_finite (fprog : Seccomp.SockFprog) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (seccompPrepareFilter fprog)) (liftSeccomp (prepare fprog)) := by
  rw [prepare_source]
  intro w pre
  rfl

theorem original_user_finite (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (seccompPrepareUserFilter fprog badFprog))
      (liftSeccomp (user fprog badFprog)) := by
  rw [user_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.SeccompFilterFinite
