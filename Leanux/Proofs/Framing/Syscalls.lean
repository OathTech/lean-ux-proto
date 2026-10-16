
/-! Closing the namespace fixture holders only runs filesystem release and
World-level work queue bookkeeping. The actual namespace cleanup is performed
later by the enclosing syscall; it is not hidden by this frame. -/
namespace Leanux.Proofs.Framing.SyscallFrames
open Leanux Std.Do Leanux.Proofs.Framing Leanux.Proofs.Framing.FSFrames

theorem netnsClose_sameWGKernel : SameWGKernel netnsClose := by
  frame_wg [netnsClose] using [sysClose_spec, taskWorkRun_spec]

theorem netnsClose_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ netnsClose
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := netnsClose_sameWGKernel.wp P

end Leanux.Proofs.Framing.SyscallFrames
