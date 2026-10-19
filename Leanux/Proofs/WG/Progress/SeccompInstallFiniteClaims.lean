import Leanux.Proofs.WG.Progress.SeccompInstallFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Concrete all-outcome installation claims. The original and finite actions
start at the same actual product state. Return values, errno and Stops agree;
no successful preparation, attachment or installation is assumed. The native
source equalities also retain exact seccomp/task stores omitted by the campaign
WG projection. These are not initialized Runner or Prefill theorems. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompInstallFinite
open Leanux Leanux.Seccomp

theorem original_mode_finite (flags : UInt32) (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (seccompSetModeFilter flags fprog badFprog))
      (liftSeccomp (mode flags fprog badFprog)) := by
  rw [mode_source]
  intro w pre
  rfl

theorem original_dispatch_finite (op : Nat) (flags : UInt32) (uargs : SeccompArgs) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (doSeccomp op flags uargs)) (liftSeccomp (dispatch op flags uargs)) := by
  rw [dispatch_source]
  intro w pre
  rfl

theorem original_prctl_finite (mode : Nat) (filter : SeccompArgs) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (prctlSetSeccomp mode filter)) (liftSeccomp (prctl mode filter)) := by
  rw [prctl_source]
  intro w pre
  rfl

theorem original_install_finite (via : InstallVia) (flags : UInt32)
    (filter : Option _root_.Leanux.ClassicProg) (len : Option Nat) (bad : BadPtr) (mode : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (sysSeccompInstall via flags filter len bad mode))
      (liftSeccomp (install via flags filter len bad mode)) := by
  rw [install_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.SeccompInstallFinite
