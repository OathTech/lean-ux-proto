import Leanux.Proofs.WG.Progress.SeccompInstallSource
import Leanux.Proofs.WG.Progress.SeccompFilterFiniteSource

/-! Complete finite concrete installation. The only nonstructural leaves were
the hidden allocations and conversion, now supplied through finite user
preparation. The original bounded attachment/cache walks and cleanup remain.
This is an equality of whole native actions, with no success premise. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompInstallFinite
open Leanux Leanux.Seccomp

def mode (flags : UInt32) (fprog : Seccomp.SockFprog) (badFprog : Bool) : Seccomp.M Int :=
  SeccompInstall.modeWith SeccompFilterFinite.user flags fprog badFprog

theorem mode_source (flags : UInt32) (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    seccompSetModeFilter flags fprog badFprog = mode flags fprog badFprog := by
  rw [SeccompInstall.mode_factor]
  unfold mode
  exact congrArg (fun callback => SeccompInstall.modeWith callback flags fprog badFprog)
    (funext fun f => funext fun b => SeccompFilterFinite.user_source f b)

def dispatch (op : Nat) (flags : UInt32) (uargs : SeccompArgs) : Seccomp.M Int :=
  SeccompInstall.dispatchWith mode op flags uargs

theorem dispatch_source (op : Nat) (flags : UInt32) (uargs : SeccompArgs) :
    doSeccomp op flags uargs = dispatch op flags uargs := by
  rw [SeccompInstall.dispatch_factor]
  unfold dispatch
  exact congrArg (fun callback => SeccompInstall.dispatchWith callback op flags uargs)
    (funext fun flags => funext fun f => funext fun b => mode_source flags f b)

def prctl (mode : Nat) (filter : SeccompArgs) : Seccomp.M Int :=
  SeccompInstall.prctlWith dispatch mode filter

theorem prctl_source (mode : Nat) (filter : SeccompArgs) :
    prctlSetSeccomp mode filter = prctl mode filter := by
  rw [SeccompInstall.prctl_factor]
  unfold prctl
  exact congrArg (fun callback => SeccompInstall.prctlWith callback mode filter)
    (funext fun op => funext fun flags => funext fun args => dispatch_source op flags args)

def install (via : InstallVia) (flags : UInt32) (filter : Option _root_.Leanux.ClassicProg)
    (len : Option Nat) (bad : BadPtr) (mode : Nat) : Seccomp.M Int :=
  SeccompInstall.installWith dispatch prctl via flags filter len bad mode

theorem install_source (via : InstallVia) (flags : UInt32)
    (filter : Option _root_.Leanux.ClassicProg) (len : Option Nat) (bad : BadPtr) (mode : Nat) :
    sysSeccompInstall via flags filter len bad mode = install via flags filter len bad mode := by
  rw [SeccompInstall.install_factor]
  unfold install
  have hd : doSeccomp = dispatch :=
    funext fun op => funext fun flags => funext fun args => dispatch_source op flags args
  have hp : prctlSetSeccomp = prctl :=
    funext fun mode => funext fun args => prctl_source mode args
  rw [hd, hp]

end Leanux.Proofs.WG.Progress.SeccompInstallFinite
