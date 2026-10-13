import Leanux.Proofs.Framing.Seccomp
import Leanux.Proofs.WG.Keypairs.Frames.Tools

/-! Legacy receive-state corollaries of the shared seccomp frames. -/
namespace Leanux.Proofs.WG.Keypairs.SeccompFrames
open Leanux Leanux.Seccomp Leanux.Proofs.Framing

theorem enterHarnessCall_sameSnapshot (nr : Int) : SameSnapshot (Leanux.Seccomp.enterHarnessCall nr) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.enterHarnessCall_sameWGKernel nr)

theorem sysSeccompProbeSelf_sameSnapshot (nr : Int) (args : Array UInt64) : SameSnapshot (Leanux.Seccomp.sysSeccompProbeSelf nr args) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompProbeSelf_sameWGKernel nr args)

theorem sysSeccompProbeChild_sameSnapshot (nr : Int) (args : Array UInt64) (strict : Option StrictVia) : SameSnapshot (Leanux.Seccomp.sysSeccompProbeChild nr args strict) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompProbeChild_sameWGKernel nr args strict)

theorem sysSeccompInstall_sameSnapshot (via : InstallVia) (flags : UInt32) (filter : Option Leanux.ClassicProg) (len : Option Nat) (bad : BadPtr) (mode : Nat) : SameSnapshot (Leanux.Seccomp.sysSeccompInstall via flags filter len bad mode) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompInstall_sameWGKernel via flags filter len bad mode)

theorem sysSeccompPrctl_sameSnapshot (cmd : PrctlCmd) (args : Array UInt64) : SameSnapshot (Leanux.Seccomp.sysSeccompPrctl cmd args) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompPrctl_sameWGKernel cmd args)

theorem sysSeccompCapdrop_sameSnapshot  : SameSnapshot (Leanux.Seccomp.sysSeccompCapdrop ) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompCapdrop_sameWGKernel )

theorem sysSeccompQuery_sameSnapshot (cmd : QueryCmd) (action flags : UInt32) : SameSnapshot (Leanux.Seccomp.sysSeccompQuery cmd action flags) :=
  sameSnapshot_of_sameWGKernel (Framing.SeccompFrames.sysSeccompQuery_sameWGKernel cmd action flags)

theorem getCurrent_sameSnapshot : SameSnapshot Leanux.getCurrent :=
  sameSnapshot_of_sameWGKernel SignalFrames.getCurrent_sameWGKernel

end Leanux.Proofs.WG.Keypairs.SeccompFrames
