import Leanux.Proofs.Framing.SeccompU

/-! Shared frames for seccomp filter state. The engine returns a pure Except;
its arbitrary successful or failing result is retained without assumptions. -/
namespace Leanux.Proofs.Framing.SeccompFrames
open Leanux Std.Do Leanux.Seccomp
open Leanux.Proofs.Framing.KernelFrames Leanux.Proofs.Framing.SignalFrames
set_option maxHeartbeats 3000000
set_option pp.structureInstances false

theorem hiddenAlloc_spec (P : WGKernelView → Prop) (site : AllocSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.hiddenAlloc site
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (Framing.hiddenAlloc_sameKernel site)).wp P

theorem refcountInc_spec (P : WGKernelView → Prop) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.refcountInc count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (Framing.refcountInc_sameKernel count)).wp P

theorem getFilter_sameWGKernel (id : FilterId) : SameWGKernel (Leanux.Seccomp.getFilter id) := by
  frame_wg [Leanux.Seccomp.getFilter] using [sbranch_spec, sbranchCmp_spec]

theorem getFilter_spec (P : WGKernelView → Prop) (id : FilterId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.getFilter id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getFilter_sameWGKernel id).wp P

theorem modifyFilter_sameWGKernel (id : FilterId) (f : SeccompFilter → SeccompFilter) : SameWGKernel (Leanux.Seccomp.modifyFilter id f) := by
  frame_wg [Leanux.Seccomp.modifyFilter] using [getFilter_spec, sbranch_spec, sbranchCmp_spec]

theorem modifyFilter_spec (P : WGKernelView → Prop) (id : FilterId) (f : SeccompFilter → SeccompFilter) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.modifyFilter id f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (modifyFilter_sameWGKernel id f).wp P

theorem modifySeccomp_sameWGKernel (f : SeccompState → SeccompState) : SameWGKernel (Leanux.Seccomp.modifySeccomp f) := by
  frame_wg [Leanux.Seccomp.modifySeccomp] using [modifyTask_spec, sbranch_spec, sbranchCmp_spec]

theorem modifySeccomp_spec (P : WGKernelView → Prop) (f : SeccompState → SeccompState) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.modifySeccomp f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (modifySeccomp_sameWGKernel f).wp P

theorem seccompUprobeException_sameWGKernel (sd : SeccompData) : SameWGKernel (Leanux.Seccomp.seccompUprobeException sd) := by
  frame_wg [Leanux.Seccomp.seccompUprobeException] using [kbranchCmp_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompUprobeException_spec (P : WGKernelView → Prop) (sd : SeccompData) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompUprobeException sd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompUprobeException_sameWGKernel sd).wp P

theorem seccompIsConstAllow_sameWGKernel (prog : _root_.Leanux.ClassicProg) (sd : SeccompData) : SameWGKernel (Leanux.Seccomp.seccompIsConstAllow prog sd) := by
  frame_wg [Leanux.Seccomp.seccompIsConstAllow] using [kbranch_spec, kbranchCmp_spec, seccompUprobeException_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompIsConstAllow_spec (P : WGKernelView → Prop) (prog : _root_.Leanux.ClassicProg) (sd : SeccompData) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompIsConstAllow prog sd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompIsConstAllow_sameWGKernel prog sd).wp P

theorem seccompCachePrepare_sameWGKernel (id : FilterId) : SameWGKernel (Leanux.Seccomp.seccompCachePrepare id) := by
  frame_wg [Leanux.Seccomp.seccompCachePrepare] using [kbranch_spec, getFilter_spec, modifyFilter_spec, seccompIsConstAllow_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompCachePrepare_spec (P : WGKernelView → Prop) (id : FilterId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompCachePrepare id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompCachePrepare_sameWGKernel id).wp P

theorem seccompCacheCheckAllow_sameWGKernel (allow : BitVec NR_syscalls) (nr : Int) : SameWGKernel (Leanux.Seccomp.seccompCacheCheckAllow allow nr) := by
  frame_wg [Leanux.Seccomp.seccompCacheCheckAllow] using [kbranch_spec, kbranchCmp_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompCacheCheckAllow_spec (P : WGKernelView → Prop) (allow : BitVec NR_syscalls) (nr : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompCacheCheckAllow allow nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompCacheCheckAllow_sameWGKernel allow nr).wp P

theorem seccompRunFilters_sameWGKernel {E : Type} [BpfEngine E] (e : E) (sd : SeccompData) : SameWGKernel (Leanux.Seccomp.seccompRunFilters e sd) := by
  frame_wg [Leanux.Seccomp.seccompRunFilters] using [getCurrent_spec, kbranch_spec, kbranchCmp_spec, getFilter_spec, seccompCacheCheckAllow_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompRunFilters_spec (P : WGKernelView → Prop) {E : Type} [BpfEngine E] (e : E) (sd : SeccompData) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompRunFilters e sd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompRunFilters_sameWGKernel e sd).wp P

theorem seccompLog_sameWGKernel (_syscall : Int) (_signr : Nat) (action : UInt32) (requested : Bool) : SameWGKernel (Leanux.Seccomp.seccompLog _syscall _signr action requested) := by
  frame_wg [Leanux.Seccomp.seccompLog] using [kbranch_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompLog_spec (P : WGKernelView → Prop) (_syscall : Int) (_signr : Nat) (action : UInt32) (requested : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompLog _syscall _signr action requested
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompLog_sameWGKernel _syscall _signr action requested).wp P

theorem seccompFilter_sameWGKernel {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : SameWGKernel (Leanux.Seccomp.seccompFilter e nr sd) := by
  frame_wg [Leanux.Seccomp.seccompFilter] using [forceSigSeccomp_spec, kbranch_spec, kbranchCmp_spec, getFilter_spec, modifySeccomp_spec, seccompRunFilters_spec, seccompLog_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompFilter_spec (P : WGKernelView → Prop) {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompFilter e nr sd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompFilter_sameWGKernel e nr sd).wp P

theorem secureComputingStrict_sameWGKernel (nr : Int) : SameWGKernel (Leanux.Seccomp.secureComputingStrict nr) := by
  frame_wg [Leanux.Seccomp.secureComputingStrict] using [kbranchCmp_spec, modifySeccomp_spec, seccompLog_spec, sbranch_spec, sbranchCmp_spec]

theorem secureComputingStrict_spec (P : WGKernelView → Prop) (nr : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.secureComputingStrict nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (secureComputingStrict_sameWGKernel nr).wp P

theorem secureComputing_sameWGKernel {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : SameWGKernel (Leanux.Seccomp.secureComputing e nr sd) := by
  frame_wg [Leanux.Seccomp.secureComputing] using [getCurrent_spec, kbranch_spec, seccompFilter_spec, secureComputingStrict_spec, sbranch_spec, sbranchCmp_spec]

theorem secureComputing_spec (P : WGKernelView → Prop) {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.secureComputing e nr sd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (secureComputing_sameWGKernel e nr sd).wp P

theorem seccompMayAssignMode_sameWGKernel (mode : SeccompMode) : SameWGKernel (Leanux.Seccomp.seccompMayAssignMode mode) := by
  frame_wg [Leanux.Seccomp.seccompMayAssignMode] using [getCurrent_spec, kbranch_spec, kbranchCmp_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompMayAssignMode_spec (P : WGKernelView → Prop) (mode : SeccompMode) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompMayAssignMode mode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompMayAssignMode_sameWGKernel mode).wp P

theorem seccompAssignMode_sameWGKernel (mode : SeccompMode) (flags : UInt32) : SameWGKernel (Leanux.Seccomp.seccompAssignMode mode flags) := by
  frame_wg [Leanux.Seccomp.seccompAssignMode] using [kbranch_spec, kflag_spec, modifySeccomp_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompAssignMode_spec (P : WGKernelView → Prop) (mode : SeccompMode) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompAssignMode mode flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompAssignMode_sameWGKernel mode flags).wp P

theorem seccompAttachFilter_sameWGKernel (flags : UInt32) (id : FilterId) : SameWGKernel (Leanux.Seccomp.seccompAttachFilter flags id) := by
  frame_wg [Leanux.Seccomp.seccompAttachFilter] using [getCurrent_spec, kbranch_spec, kbranchCmp_spec, kflag_spec, getFilter_spec, modifyFilter_spec, modifySeccomp_spec, seccompCachePrepare_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompAttachFilter_spec (P : WGKernelView → Prop) (flags : UInt32) (id : FilterId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompAttachFilter flags id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompAttachFilter_sameWGKernel flags id).wp P

theorem seccompFilterFree_sameWGKernel (prepared : Option FilterId) : SameWGKernel (Leanux.Seccomp.seccompFilterFree prepared) := by
  frame_wg [Leanux.Seccomp.seccompFilterFree] using [kbranch_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompFilterFree_spec (P : WGKernelView → Prop) (prepared : Option FilterId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompFilterFree prepared
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompFilterFree_sameWGKernel prepared).wp P

theorem seccompPrepareFilter_sameWGKernel (fprog : SockFprog) : SameWGKernel (Leanux.Seccomp.seccompPrepareFilter fprog) := by
  frame_wg [Leanux.Seccomp.seccompPrepareFilter] using [getCurrent_spec, kbranch_spec, kbranchCmp_spec, hiddenAlloc_spec, bpfProgCreateFromUser_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompPrepareFilter_spec (P : WGKernelView → Prop) (fprog : SockFprog) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompPrepareFilter fprog
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompPrepareFilter_sameWGKernel fprog).wp P

theorem seccompPrepareUserFilter_sameWGKernel (fprog : SockFprog) (badFprog : Bool) : SameWGKernel (Leanux.Seccomp.seccompPrepareUserFilter fprog badFprog) := by
  frame_wg [Leanux.Seccomp.seccompPrepareUserFilter] using [kbranch_spec, seccompPrepareFilter_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompPrepareUserFilter_spec (P : WGKernelView → Prop) (fprog : SockFprog) (badFprog : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompPrepareUserFilter fprog badFprog
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompPrepareUserFilter_sameWGKernel fprog badFprog).wp P

theorem hasDuplicateListener_sameWGKernel  : SameWGKernel (Leanux.Seccomp.hasDuplicateListener ) := by
  frame_wg [Leanux.Seccomp.hasDuplicateListener] using [kbranch_spec, sbranch_spec, sbranchCmp_spec]

theorem hasDuplicateListener_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.hasDuplicateListener
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (hasDuplicateListener_sameWGKernel ).wp P

theorem seccompSetModeFilter_sameWGKernel (flags : UInt32) (fprog : SockFprog) (badFprog : Bool) : SameWGKernel (Leanux.Seccomp.seccompSetModeFilter flags fprog badFprog) := by
  frame_wg [Leanux.Seccomp.seccompSetModeFilter] using [kbranch_spec, kbranchCmp_spec, kflag_spec, seccompMayAssignMode_spec, seccompAssignMode_spec, seccompAttachFilter_spec, seccompFilterFree_spec, seccompPrepareUserFilter_spec, hasDuplicateListener_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompSetModeFilter_spec (P : WGKernelView → Prop) (flags : UInt32) (fprog : SockFprog) (badFprog : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompSetModeFilter flags fprog badFprog
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompSetModeFilter_sameWGKernel flags fprog badFprog).wp P

theorem seccompSetModeStrict_sameWGKernel  : SameWGKernel (Leanux.Seccomp.seccompSetModeStrict ) := by
  frame_wg [Leanux.Seccomp.seccompSetModeStrict] using [kbranch_spec, seccompMayAssignMode_spec, seccompAssignMode_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompSetModeStrict_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompSetModeStrict
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompSetModeStrict_sameWGKernel ).wp P

theorem seccompGetActionAvail_sameWGKernel (action : UInt32) : SameWGKernel (Leanux.Seccomp.seccompGetActionAvail action) := by
  frame_wg [Leanux.Seccomp.seccompGetActionAvail] using [kbranch_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompGetActionAvail_spec (P : WGKernelView → Prop) (action : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompGetActionAvail action
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompGetActionAvail_sameWGKernel action).wp P

theorem seccompGetNotifSizes_sameWGKernel  : SameWGKernel (Leanux.Seccomp.seccompGetNotifSizes ) := by
  frame_wg [Leanux.Seccomp.seccompGetNotifSizes] using [kbranch_spec, sbranch_spec, sbranchCmp_spec]

theorem seccompGetNotifSizes_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.seccompGetNotifSizes
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompGetNotifSizes_sameWGKernel ).wp P

theorem doSeccomp_sameWGKernel (op : Nat) (flags : UInt32) (uargs : SeccompArgs) : SameWGKernel (Leanux.Seccomp.doSeccomp op flags uargs) := by
  unfold Leanux.Seccomp.doSeccomp
  frame_wg [] using [kbranch_spec, kbranchCmp_spec, seccompSetModeFilter_spec, seccompSetModeStrict_spec, seccompGetActionAvail_spec, seccompGetNotifSizes_spec, sbranch_spec, sbranchCmp_spec]

theorem doSeccomp_spec (P : WGKernelView → Prop) (op : Nat) (flags : UInt32) (uargs : SeccompArgs) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.doSeccomp op flags uargs
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doSeccomp_sameWGKernel op flags uargs).wp P

theorem prctlSetSeccomp_sameWGKernel (mode : Nat) (filter : SeccompArgs) : SameWGKernel (Leanux.Seccomp.prctlSetSeccomp mode filter) := by
  frame_wg [Leanux.Seccomp.prctlSetSeccomp] using [kbranch_spec, doSeccomp_spec, sbranch_spec, sbranchCmp_spec]

theorem prctlSetSeccomp_spec (P : WGKernelView → Prop) (mode : Nat) (filter : SeccompArgs) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.prctlSetSeccomp mode filter
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (prctlSetSeccomp_sameWGKernel mode filter).wp P

theorem prctlGetSeccomp_sameWGKernel  : SameWGKernel (Leanux.Seccomp.prctlGetSeccomp ) := by
  frame_wg [Leanux.Seccomp.prctlGetSeccomp] using [getCurrent_spec, sbranch_spec, sbranchCmp_spec]

theorem prctlGetSeccomp_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.prctlGetSeccomp
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (prctlGetSeccomp_sameWGKernel ).wp P

theorem getSeccompFilter_sameWGKernel (t : TaskRef) : SameWGKernel (Leanux.Seccomp.getSeccompFilter t) := by
  frame_wg [Leanux.Seccomp.getSeccompFilter] using [getTask_spec, kbranch_spec, refcountInc_spec, getFilter_spec, modifyFilter_spec, sbranch_spec, sbranchCmp_spec]

theorem getSeccompFilter_spec (P : WGKernelView → Prop) (t : TaskRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.Seccomp.getSeccompFilter t
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getSeccompFilter_sameWGKernel t).wp P

end Leanux.Proofs.Framing.SeccompFrames
