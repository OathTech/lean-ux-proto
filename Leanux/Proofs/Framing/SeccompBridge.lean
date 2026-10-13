import Leanux.Proofs.Framing.Signal
import Leanux.Seccomp.Filter

/-! Full WireGuard frames for seccomp record consumers and the concrete U bridge. -/
namespace Leanux.Proofs.Framing.SeccompFrames
open Leanux Std.Do Leanux.Seccomp Leanux.Proofs.Framing.KernelFrames
open Leanux.Proofs.Framing.SignalFrames
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

theorem emit_sameWGKernel (d : Decision) (o : Bool) (ops : Option (Int × Int)) : SameWGKernel (Leanux.Seccomp.emit d o ops) := by
  frame_wg [Leanux.Seccomp.emit] using []

theorem emit_spec (P : WGKernelView → Prop) (d : Decision) (o : Bool) (ops : Option (Int × Int)) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.emit d o ops
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (emit_sameWGKernel d o ops).wp P

theorem kbranch_sameWGKernel (d : Decision) (o : Bool) : SameWGKernel (Leanux.Seccomp.kbranch d o) := by
  frame_wg [Leanux.Seccomp.kbranch] using [emit_spec]

theorem kbranch_spec (P : WGKernelView → Prop) (d : Decision) (o : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.kbranch d o
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (kbranch_sameWGKernel d o).wp P

theorem kbranchCmp_sameWGKernel (d : Decision) (o : Bool) (a b : Int) : SameWGKernel (Leanux.Seccomp.kbranchCmp d o a b) := by
  frame_wg [Leanux.Seccomp.kbranchCmp] using [emit_spec]

theorem kbranchCmp_spec (P : WGKernelView → Prop) (d : Decision) (o : Bool) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.kbranchCmp d o a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (kbranchCmp_sameWGKernel d o a b).wp P

theorem kflag_sameWGKernel (d : Decision) (x mask : UInt32) : SameWGKernel (Leanux.Seccomp.kflag d x mask) := by
  frame_wg [Leanux.Seccomp.kflag] using [kbranchCmp_spec]

theorem kflag_spec (P : WGKernelView → Prop) (d : Decision) (x mask : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.kflag d x mask
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (kflag_sameWGKernel d x mask).wp P

theorem sbranch_sameWGKernel (d : SDecision) (o : Bool) : SameWGKernel (SeccompM.branch (m := M) d o) := by
  exact kbranch_sameWGKernel _ _

theorem sbranch_spec (P : WGKernelView → Prop) (d : SDecision) (o : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.branch (m := M) d o
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sbranch_sameWGKernel d o).wp P

theorem sbranchCmp_sameWGKernel (d : SDecision) (o : Bool) (a b : Int) : SameWGKernel (SeccompM.branchCmp (m := M) d o a b) := by
  exact kbranchCmp_sameWGKernel _ _ _ _

theorem sbranchCmp_spec (P : WGKernelView → Prop) (d : SDecision) (o : Bool) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.branchCmp (m := M) d o a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sbranchCmp_sameWGKernel d o a b).wp P

theorem salloc_sameWGKernel (site : SAllocSite) : SameWGKernel (SeccompM.alloc (m := M) site) := by
  exact sameWGKernel_of_sameKernel (hiddenAlloc_sameKernel _)

theorem salloc_spec (P : WGKernelView → Prop) (site : SAllocSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.alloc (m := M) site
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (salloc_sameWGKernel site).wp P

theorem stranslatedInsn_sameWGKernel  : SameWGKernel (SeccompM.translatedInsn (m := M)) := by
  frame_wg [SeccompM.translatedInsn] using [hiddenU64_spec]

theorem stranslatedInsn_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.translatedInsn (m := M)
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (stranslatedInsn_sameWGKernel ).wp P

theorem stranslatedLen_sameWGKernel  : SameWGKernel (SeccompM.translatedLen (m := M)) := by
  frame_wg [SeccompM.translatedLen] using []

theorem stranslatedLen_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.translatedLen (m := M)
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (stranslatedLen_sameWGKernel ).wp P

theorem srecordMismatch_sameWGKernel {α : Type} (what : String) : SameWGKernel (SeccompM.recordMismatch (m := M) (α := α) what) := by
  frame_wg [SeccompM.recordMismatch] using []

theorem srecordMismatch_spec (P : WGKernelView → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.recordMismatch (m := M) (α := α) what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (srecordMismatch_sameWGKernel what).wp P

theorem sunsupported_sameWGKernel {α : Type} (what : String) : SameWGKernel (SeccompM.unsupported (m := M) (α := α) what) := by
  frame_wg [SeccompM.unsupported] using []

theorem sunsupported_spec (P : WGKernelView → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.unsupported (m := M) (α := α) what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sunsupported_sameWGKernel what).wp P

theorem sinvariant_sameWGKernel {α : Type} (what : String) : SameWGKernel (SeccompM.invariant (m := M) (α := α) what) := by
  frame_wg [SeccompM.invariant] using []

theorem sinvariant_spec (P : WGKernelView → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ SeccompM.invariant (m := M) (α := α) what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sinvariant_sameWGKernel what).wp P

theorem cmpEq_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpEq (m := M) d a b) := by
  frame_wg [cmpEq] using [sbranchCmp_spec]

theorem cmpEq_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpEq (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpEq_sameWGKernel d a b).wp P

theorem cmpNe_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpNe (m := M) d a b) := by
  frame_wg [cmpNe] using [sbranchCmp_spec]

theorem cmpNe_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpNe (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpNe_sameWGKernel d a b).wp P

theorem cmpLt_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpLt (m := M) d a b) := by
  frame_wg [cmpLt] using [sbranchCmp_spec]

theorem cmpLt_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpLt (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpLt_sameWGKernel d a b).wp P

theorem cmpLe_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpLe (m := M) d a b) := by
  frame_wg [cmpLe] using [sbranchCmp_spec]

theorem cmpLe_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpLe (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpLe_sameWGKernel d a b).wp P

theorem cmpGt_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpGt (m := M) d a b) := by
  frame_wg [cmpGt] using [sbranchCmp_spec]

theorem cmpGt_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpGt (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpGt_sameWGKernel d a b).wp P

theorem cmpGe_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpGe (m := M) d a b) := by
  frame_wg [cmpGe] using [sbranchCmp_spec]

theorem cmpGe_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpGe (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpGe_sameWGKernel d a b).wp P

theorem cmpFlag_sameWGKernel (d : SDecision) (a b : Int) : SameWGKernel (cmpFlag (m := M) d a b) := by
  frame_wg [cmpFlag] using [sbranchCmp_spec]

theorem cmpFlag_spec (P : WGKernelView → Prop) (d : SDecision) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ cmpFlag (m := M) d a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (cmpFlag_sameWGKernel d a b).wp P

theorem cmpGt_result (d : SDecision) (a b : Int) :
    ⦃⌜True⌝⦄ cmpGt (m := M) d a b ⦃⇓? r _ => ⌜r = decide (a > b)⌝⦄ := by
  have es := emit_spec (fun _ => True)
  mvcgen [cmpGt, SeccompM.branchCmp, kbranchCmp, es]

end Leanux.Proofs.Framing.SeccompFrames
