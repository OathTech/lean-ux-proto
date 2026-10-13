import Leanux.Proofs.Framing.SeccompFilter

import Leanux.Seccomp.Syscalls

/-! Seccomp syscall and environment effects preserve the full WireGuard view. -/
namespace Leanux.Proofs.Framing.SeccompFrames
open Lean Leanux Std.Do Leanux.Seccomp
open Leanux.Proofs.Framing.KernelFrames Leanux.Proofs.Framing.SignalFrames
set_option maxHeartbeats 3000000
set_option pp.structureInstances false

theorem forkClocks_sameWGKernel  : SameWGKernel (Leanux.Env.forkClocks) := by
  frame_wg [Leanux.Env.forkClocks] using [hidden_spec]

theorem forkClocks_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Env.forkClocks
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (forkClocks_sameWGKernel ).wp P

theorem childCreate_sameWGKernel  : SameWGKernel (Leanux.Env.childCreate) := by
  frame_wg [Leanux.Env.childCreate] using []

theorem childCreate_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Env.childCreate
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (childCreate_sameWGKernel ).wp P

theorem childExit_sameWGKernel  : SameWGKernel (Leanux.Env.childExit) := by
  frame_wg [Leanux.Env.childExit] using []

theorem childExit_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Env.childExit
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (childExit_sameWGKernel ).wp P

theorem childDrop_sameWGKernel  : SameWGKernel (Leanux.Env.childDrop) := by
  frame_wg [Leanux.Env.childDrop] using []

theorem childDrop_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Env.childDrop
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (childDrop_sameWGKernel ).wp P

theorem trapDelivered_sameWGKernel  : SameWGKernel (Leanux.Env.trapDelivered) := by
  frame_wg [Leanux.Env.trapDelivered] using [modifyTask_spec]

theorem trapDelivered_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Env.trapDelivered
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (trapDelivered_sameWGKernel ).wp P

theorem enterSyscall_sameWGKernel (nr : Int) (args : Array UInt64 := zeroArgs) : SameWGKernel (Leanux.Seccomp.enterSyscall nr args) := by
  frame_wg [Leanux.Seccomp.enterSyscall] using [getCurrent_spec, secureComputing_spec]

theorem enterSyscall_spec (P : WGKernelView → Prop) (nr : Int) (args : Array UInt64 := zeroArgs) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.enterSyscall nr args
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (enterSyscall_sameWGKernel nr args).wp P

theorem enterHarnessCall_sameWGKernel (nr : Int) : SameWGKernel (Leanux.Seccomp.enterHarnessCall nr) := by
  frame_wg [Leanux.Seccomp.enterHarnessCall] using [getCurrent_spec, getFilter_spec, secureComputing_spec]

theorem enterHarnessCall_spec (P : WGKernelView → Prop) (nr : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.enterHarnessCall nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (enterHarnessCall_sameWGKernel nr).wp P

theorem probeResult_sameWGKernel (nr : Int) : SameWGKernel (Leanux.Seccomp.probeResult nr) := by
  frame_wg [Leanux.Seccomp.probeResult] using []

theorem probeResult_spec (P : WGKernelView → Prop) (nr : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.probeResult nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (probeResult_sameWGKernel nr).wp P

theorem trapReturn_sameWGKernel (nr _data : Int) : SameWGKernel (Leanux.Seccomp.trapReturn nr _data) := by
  frame_wg [Leanux.Seccomp.trapReturn] using [trapDelivered_spec, enterHarnessCall_spec]

theorem trapReturn_spec (P : WGKernelView → Prop) (nr _data : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.trapReturn nr _data
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (trapReturn_sameWGKernel nr _data).wp P

theorem probeOut_sameWGKernel (sigsys : Json) (child : Json) : SameWGKernel (Leanux.Seccomp.probeOut sigsys child) := by
  frame_wg [Leanux.Seccomp.probeOut] using []

theorem probeOut_spec (P : WGKernelView → Prop) (sigsys : Json) (child : Json) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.probeOut sigsys child
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (probeOut_sameWGKernel sigsys child).wp P

theorem sysSeccompProbeSelf_sameWGKernel (nr : Int) (args : Array UInt64) : SameWGKernel (Leanux.Seccomp.sysSeccompProbeSelf nr args) := by
  frame_wg [Leanux.Seccomp.sysSeccompProbeSelf] using [enterSyscall_spec, probeResult_spec, trapReturn_spec, probeOut_spec]

theorem sysSeccompProbeSelf_spec (P : WGKernelView → Prop) (nr : Int) (args : Array UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompProbeSelf nr args
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompProbeSelf_sameWGKernel nr args).wp P

theorem sysSeccompProbeChild_sameWGKernel (nr : Int) (args : Array UInt64) (strict : Option StrictVia) : SameWGKernel (Leanux.Seccomp.sysSeccompProbeChild nr args strict) := by
  cases strict with
  | none =>
    frame_wg [Leanux.Seccomp.sysSeccompProbeChild] using [doSeccomp_spec, prctlSetSeccomp_spec, getSeccompFilter_spec, forkClocks_spec, childCreate_spec, childExit_spec, childDrop_spec, enterSyscall_spec, enterHarnessCall_spec, probeResult_spec, trapReturn_spec, probeOut_spec]
  | some via =>
    cases via <;>
      frame_wg [Leanux.Seccomp.sysSeccompProbeChild] using [doSeccomp_spec, prctlSetSeccomp_spec, getSeccompFilter_spec, forkClocks_spec, childCreate_spec, childExit_spec, childDrop_spec, enterSyscall_spec, enterHarnessCall_spec, probeResult_spec, trapReturn_spec, probeOut_spec]

theorem sysSeccompProbeChild_spec (P : WGKernelView → Prop) (nr : Int) (args : Array UInt64) (strict : Option StrictVia) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompProbeChild nr args strict
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompProbeChild_sameWGKernel nr args strict).wp P

theorem sysSeccompInstall_sameWGKernel (via : InstallVia) (flags : UInt32) (filter : Option _root_.Leanux.ClassicProg)
    (len : Option Nat) (bad : BadPtr) (mode : Nat) : SameWGKernel (Leanux.Seccomp.sysSeccompInstall via flags filter len bad mode) := by
  frame_wg [Leanux.Seccomp.sysSeccompInstall] using [doSeccomp_spec, prctlSetSeccomp_spec]

theorem sysSeccompInstall_spec (P : WGKernelView → Prop) (via : InstallVia) (flags : UInt32) (filter : Option _root_.Leanux.ClassicProg)
    (len : Option Nat) (bad : BadPtr) (mode : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompInstall via flags filter len bad mode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompInstall_sameWGKernel via flags filter len bad mode).wp P

theorem sysSeccompPrctl_sameWGKernel (cmd : PrctlCmd) (args : Array UInt64) : SameWGKernel (Leanux.Seccomp.sysSeccompPrctl cmd args) := by
  frame_wg [Leanux.Seccomp.sysSeccompPrctl] using [getTask_spec, modifyTask_spec, prctlGetSeccomp_spec]

theorem sysSeccompPrctl_spec (P : WGKernelView → Prop) (cmd : PrctlCmd) (args : Array UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompPrctl cmd args
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompPrctl_sameWGKernel cmd args).wp P

theorem sysSeccompCapdrop_sameWGKernel  : SameWGKernel (Leanux.Seccomp.sysSeccompCapdrop ) := by
  frame_wg [Leanux.Seccomp.sysSeccompCapdrop] using [modifyTask_spec]

theorem sysSeccompCapdrop_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompCapdrop
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompCapdrop_sameWGKernel ).wp P

theorem sysSeccompQuery_sameWGKernel (cmd : QueryCmd) (action flags : UInt32) : SameWGKernel (Leanux.Seccomp.sysSeccompQuery cmd action flags) := by
  frame_wg [Leanux.Seccomp.sysSeccompQuery] using [doSeccomp_spec]

theorem sysSeccompQuery_spec (P : WGKernelView → Prop) (cmd : QueryCmd) (action flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.sysSeccompQuery cmd action flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysSeccompQuery_sameWGKernel cmd action flags).wp P

end Leanux.Proofs.Framing.SeccompFrames
