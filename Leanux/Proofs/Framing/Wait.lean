import Leanux.Proofs.Framing.Kernel
import Leanux.FS.Wait

/-! Full WireGuard kernel framing for the wait-queue service (`Leanux/FS/Wait.lean`,
the epoll carry-over of 2026-10-13): the epoll stores, the heads, queueing,
and the wake walk with the callback it runs. The walk and the callback are
one mutual group bounded by a nesting fuel, so they are framed together by
induction on the fuel; the group preserves the complete WireGuard kernel view. -/
namespace Leanux.Proofs.Framing.WaitFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing.KernelFrames

/-! ## The epoll stores (`Leanux/Kernel/Defs.lean`) -/

theorem getEp_sameWGKernel (id : EpId) : SameWGKernel (Leanux.getEp id) := by
  frame_wg [getEp] using []

theorem getEp_spec (P : WGKernelView → Prop) (id : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getEp id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getEp_sameWGKernel id).wp P

theorem setEp_sameWGKernel (id : EpId) (e : Eventpoll) : SameWGKernel (Leanux.setEp id e) := by
  frame_wg [setEp] using []

theorem setEp_spec (P : WGKernelView → Prop) (id : EpId) (e : Eventpoll) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setEp id e
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setEp_sameWGKernel id e).wp P

theorem freeEp_sameWGKernel (id : EpId) : SameWGKernel (Leanux.freeEp id) := by
  frame_wg [freeEp] using []

theorem freeEp_spec (P : WGKernelView → Prop) (id : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freeEp id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freeEp_sameWGKernel id).wp P

theorem getEpi_sameWGKernel (id : EpiId) : SameWGKernel (Leanux.getEpi id) := by
  frame_wg [getEpi] using []

theorem getEpi_spec (P : WGKernelView → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getEpi id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getEpi_sameWGKernel id).wp P

theorem setEpi_sameWGKernel (id : EpiId) (e : Epitem) : SameWGKernel (Leanux.setEpi id e) := by
  frame_wg [setEpi] using []

theorem setEpi_spec (P : WGKernelView → Prop) (id : EpiId) (e : Epitem) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setEpi id e
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setEpi_sameWGKernel id e).wp P

theorem freeEpi_sameWGKernel (id : EpiId) : SameWGKernel (Leanux.freeEpi id) := by
  frame_wg [freeEpi] using []

theorem freeEpi_spec (P : WGKernelView → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freeEpi id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freeEpi_sameWGKernel id).wp P

theorem getPwq_sameWGKernel (id : PwqId) : SameWGKernel (Leanux.getPwq id) := by
  frame_wg [getPwq] using []

theorem getPwq_spec (P : WGKernelView → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPwq id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getPwq_sameWGKernel id).wp P

theorem setPwq_sameWGKernel (id : PwqId) (p : EppollEntry) : SameWGKernel (Leanux.setPwq id p) := by
  frame_wg [setPwq] using []

theorem setPwq_spec (P : WGKernelView → Prop) (id : PwqId) (p : EppollEntry) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setPwq id p
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setPwq_sameWGKernel id p).wp P

theorem freePwq_sameWGKernel (id : PwqId) : SameWGKernel (Leanux.freePwq id) := by
  frame_wg [freePwq] using []

theorem freePwq_spec (P : WGKernelView → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freePwq id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freePwq_sameWGKernel id).wp P

/-! ## The heads and queueing -/

theorem getWaitQueue_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.getWaitQueue r) := by
  cases r <;> frame_wg [getWaitQueue] using [getPipe_spec, getCtx_spec, getEp_spec]

theorem getWaitQueue_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getWaitQueue r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getWaitQueue_sameWGKernel r).wp P

theorem setWaitQueue_sameWGKernel (r : WaitQueueRef) (q : WaitQueue) : SameWGKernel (Leanux.setWaitQueue r q) := by
  cases r <;> frame_wg [setWaitQueue] using [getPipe_spec, setPipe_spec, getCtx_spec, setCtx_spec,
    getEp_spec, setEp_spec]

theorem setWaitQueue_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (q : WaitQueue) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setWaitQueue r q
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setWaitQueue_sameWGKernel r q).wp P

theorem waitqueueActive_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.waitqueueActive r) := by
  frame_wg [waitqueueActive] using [getWaitQueue_spec]

theorem waitqueueActive_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.waitqueueActive r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (waitqueueActive_sameWGKernel r).wp P

theorem addWaitQueue_sameWGKernel (r : WaitQueueRef) (e : WaitEntry) : SameWGKernel (Leanux.addWaitQueue r e) := by
  frame_wg [addWaitQueue] using [getWaitQueue_spec, setWaitQueue_spec]

theorem addWaitQueue_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.addWaitQueue r e
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (addWaitQueue_sameWGKernel r e).wp P

theorem addWaitQueueExclusive_sameWGKernel (r : WaitQueueRef) (e : WaitEntry) :
    SameWGKernel (Leanux.addWaitQueueExclusive r e) := by
  frame_wg [addWaitQueueExclusive] using [getWaitQueue_spec, setWaitQueue_spec]

theorem addWaitQueueExclusive_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.addWaitQueueExclusive r e
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (addWaitQueueExclusive_sameWGKernel r e).wp P

theorem removeWaitQueue_sameWGKernel (r : WaitQueueRef) (e : WaitEntry) :
    SameWGKernel (Leanux.removeWaitQueue r e) := by
  frame_wg [removeWaitQueue] using [getWaitQueue_spec, setWaitQueue_spec]

theorem removeWaitQueue_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.removeWaitQueue r e
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (removeWaitQueue_sameWGKernel r e).wp P

/-! ## The wake walk and its callback, by induction on the nesting fuel

At fuel `n + 1` the walk calls the entries at fuel `n`; the callback, the
safewake and the entry call at a given fuel chain through the walk at that
same fuel. So one induction: the walk at `0` makes no call, the walk at
`n + 1` uses the entry call at `n`, and the rest of each level follows. -/

/-- The three callers at one fuel, given the walk at that fuel. -/
theorem chain_of_common (fuel : Nat)
    (hcommon : ∀ (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) :
    (∀ (P : WGKernelView → Prop) (ep : EpId) (epi : Option EpiId) (pollflags : UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPollSafewakeAt fuel ep epi pollflags
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) ∧
    (∀ (P : WGKernelView → Prop) (pwq : PwqId) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPollCallbackAt fuel pwq mode wakeFlags key
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) ∧
    (∀ (P : WGKernelView → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ e.callAt fuel mode wakeFlags key
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) := by
  have safewake : ∀ ep epi pollflags, SameWGKernel (Leanux.epPollSafewakeAt fuel ep epi pollflags) := by
    intro ep epi pollflags
    frame_wg [epPollSafewakeAt] using [hcommon]
  have safewake_spec := fun P ep epi pollflags => (safewake ep epi pollflags).wp P
  have callback : ∀ pwq mode wakeFlags key,
      SameWGKernel (Leanux.epPollCallbackAt fuel pwq mode wakeFlags key) := by
    intro pwq mode wakeFlags key
    frame_wg [epPollCallbackAt] using [getPwq_spec, getEpi_spec, getEp_spec, setEp_spec,
      setEpi_spec, waitqueueActive_spec, safewake_spec]
  have callback_spec := fun P pwq mode wakeFlags key => (callback pwq mode wakeFlags key).wp P
  have call : ∀ (e : WaitEntry) mode wakeFlags key, SameWGKernel (e.callAt fuel mode wakeFlags key) := by
    intro e mode wakeFlags key
    obtain ⟨⟨pwq⟩, exclusive⟩ := e
    frame_wg [WaitEntry.callAt] using [callback_spec]
  exact ⟨safewake_spec, callback_spec, fun P e mode wakeFlags key => (call e mode wakeFlags key).wp P⟩

/-- The walk at fuel `n + 1`, given the entry call at fuel `n`. -/
theorem common_succ (n : Nat)
    (hcall : ∀ (P : WGKernelView → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ e.callAt n mode wakeFlags key ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄)
    (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32) (key : Option UInt32) :
    SameWGKernel (Leanux.wakeUpCommonAt (n + 1) r mode nrExclusive wakeFlags key) := by
  frame_wg [wakeUpCommonAt] using [getWaitQueue_spec, hcall]

/-- The walk at fuel `0` makes no call. -/
theorem common_zero (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : SameWGKernel (Leanux.wakeUpCommonAt 0 r mode nrExclusive wakeFlags key) := by
  frame_wg [wakeUpCommonAt] using [getWaitQueue_spec]

theorem wakeAt_specs (fuel : Nat) :
    (∀ (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) ∧
    (∀ (P : WGKernelView → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ e.callAt fuel mode wakeFlags key
      ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) := by
  induction fuel with
  | zero =>
    have common_spec := fun P r mode nrExclusive wakeFlags key =>
      (common_zero r mode nrExclusive wakeFlags key).wp P
    exact ⟨common_spec, (chain_of_common 0 common_spec).2.2⟩
  | succ n ih =>
    have common_spec := fun P r mode nrExclusive wakeFlags key =>
      (common_succ n ih.2 r mode nrExclusive wakeFlags key).wp P
    exact ⟨common_spec, (chain_of_common (n + 1) common_spec).2.2⟩

theorem wakeUpCommonAt_spec (P : WGKernelView → Prop) (fuel : Nat) (r : WaitQueueRef) (mode : UInt32)
    (nrExclusive : Int) (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeAt_specs fuel).1 P r mode nrExclusive wakeFlags key

theorem epPollSafewakeAt_spec (P : WGKernelView → Prop) (fuel : Nat) (ep : EpId) (epi : Option EpiId)
    (pollflags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPollSafewakeAt fuel ep epi pollflags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (chain_of_common fuel ((wakeAt_specs fuel).1)).1 P ep epi pollflags

theorem epPollCallbackAt_spec (P : WGKernelView → Prop) (fuel : Nat) (pwq : PwqId) (mode wakeFlags : UInt32)
    (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPollCallbackAt fuel pwq mode wakeFlags key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (chain_of_common fuel ((wakeAt_specs fuel).1)).2.1 P pwq mode wakeFlags key

/-! ## The wakes at the top of a walk and the macros -/

theorem wakeUpCommon_sameWGKernel (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : SameWGKernel (Leanux.wakeUpCommon r mode nrExclusive wakeFlags key) := by
  frame_wg [wakeUpCommon] using [wakeUpCommonAt_spec]

theorem wakeUpCommon_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpCommon r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpCommon_sameWGKernel r mode nrExclusive wakeFlags key).wp P

theorem epPollSafewake_sameWGKernel (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    SameWGKernel (Leanux.epPollSafewake ep epi pollflags) := by
  frame_wg [epPollSafewake] using [epPollSafewakeAt_spec]

theorem epPollSafewake_spec (P : WGKernelView → Prop) (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPollSafewake ep epi pollflags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epPollSafewake_sameWGKernel ep epi pollflags).wp P

theorem wakeUpCommonLock_sameWGKernel (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    SameWGKernel (Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key) := by
  frame_wg [wakeUpCommonLock] using [wakeUpCommon_spec]

theorem wakeUpCommonLock_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpCommonLock_sameWGKernel r mode nrExclusive wakeFlags key).wp P

theorem wakeUpBase_sameWGKernel (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    SameWGKernel (Leanux.wakeUpBase r mode nr key) := by
  frame_wg [wakeUpBase] using [wakeUpCommonLock_spec]

theorem wakeUpBase_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpBase r mode nr key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpBase_sameWGKernel r mode nr key).wp P

theorem wakeUpLockedKey_sameWGKernel (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameWGKernel (Leanux.wakeUpLockedKey r mode key) := by
  frame_wg [wakeUpLockedKey] using [wakeUpCommon_spec]

theorem wakeUpLockedKey_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpLockedKey r mode key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpLockedKey_sameWGKernel r mode key).wp P

theorem wakeUpSyncKey_sameWGKernel (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameWGKernel (Leanux.wakeUpSyncKey r mode key) := by
  frame_wg [wakeUpSyncKey] using [wakeUpCommonLock_spec]

theorem wakeUpSyncKey_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpSyncKey r mode key
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpSyncKey_sameWGKernel r mode key).wp P

theorem wakeUp_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.wakeUp r) := by
  frame_wg [wakeUp] using [wakeUpBase_spec]

theorem wakeUp_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUp r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUp_sameWGKernel r).wp P

theorem wakeUpAll_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.wakeUpAll r) := by
  frame_wg [wakeUpAll] using [wakeUpBase_spec]

theorem wakeUpAll_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpAll r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpAll_sameWGKernel r).wp P

theorem wakeUpSync_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.wakeUpSync r) := by
  frame_wg [wakeUpSync] using [wakeUpSyncKey_spec]

theorem wakeUpSync_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpSync r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpSync_sameWGKernel r).wp P

theorem wakeUpInterruptible_sameWGKernel (r : WaitQueueRef) : SameWGKernel (Leanux.wakeUpInterruptible r) := by
  frame_wg [wakeUpInterruptible] using [wakeUpBase_spec]

theorem wakeUpInterruptible_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpInterruptible r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpInterruptible_sameWGKernel r).wp P

theorem wakeUpInterruptibleAll_sameWGKernel (r : WaitQueueRef) :
    SameWGKernel (Leanux.wakeUpInterruptibleAll r) := by
  frame_wg [wakeUpInterruptibleAll] using [wakeUpBase_spec]

theorem wakeUpInterruptibleAll_spec (P : WGKernelView → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpInterruptibleAll r
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpInterruptibleAll_sameWGKernel r).wp P

theorem wakeUpPoll_sameWGKernel (r : WaitQueueRef) (m : UInt32) : SameWGKernel (Leanux.wakeUpPoll r m) := by
  frame_wg [wakeUpPoll] using [wakeUpBase_spec]

theorem wakeUpPoll_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpPoll r m
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpPoll_sameWGKernel r m).wp P

theorem wakeUpLockedPoll_sameWGKernel (r : WaitQueueRef) (m : UInt32) :
    SameWGKernel (Leanux.wakeUpLockedPoll r m) := by
  frame_wg [wakeUpLockedPoll] using [wakeUpLockedKey_spec]

theorem wakeUpLockedPoll_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpLockedPoll r m
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpLockedPoll_sameWGKernel r m).wp P

theorem wakeUpInterruptibleSyncPoll_sameWGKernel (r : WaitQueueRef) (m : UInt32) :
    SameWGKernel (Leanux.wakeUpInterruptibleSyncPoll r m) := by
  frame_wg [wakeUpInterruptibleSyncPoll] using [wakeUpSyncKey_spec]

theorem wakeUpInterruptibleSyncPoll_spec (P : WGKernelView → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.wakeUpInterruptibleSyncPoll r m
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wakeUpInterruptibleSyncPoll_sameWGKernel r m).wp P

end Leanux.Proofs.Framing.WaitFrames
