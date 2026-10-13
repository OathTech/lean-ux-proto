import Leanux.Proofs.WG.Keypairs.Frames.Kernel
import Leanux.FS.Wait

/-! Receive-state framing for the wait-queue service (`Leanux/FS/Wait.lean`,
the epoll carry-over of 2026-10-13): the epoll stores, the heads, queueing,
and the wake walk with the callback it runs. The walk and the callback are
one mutual group bounded by a nesting fuel, so they are framed together by
induction on the fuel; nothing in the group touches the keypair store. -/
namespace Leanux.Proofs.WG.Keypairs.WaitFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames

/-! ## The epoll stores (`Leanux/Kernel/Defs.lean`) -/

theorem getEp_sameSnapshot (id : EpId) : SameSnapshot (Leanux.getEp id) := by
  frame_same [getEp] using []

theorem getEp_spec (P : Snapshot → Prop) (id : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getEp id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getEp_sameSnapshot id).wp P

theorem setEp_sameSnapshot (id : EpId) (e : Eventpoll) : SameSnapshot (Leanux.setEp id e) := by
  frame_same [setEp] using []

theorem setEp_spec (P : Snapshot → Prop) (id : EpId) (e : Eventpoll) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setEp id e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setEp_sameSnapshot id e).wp P

theorem freeEp_sameSnapshot (id : EpId) : SameSnapshot (Leanux.freeEp id) := by
  frame_same [freeEp] using []

theorem freeEp_spec (P : Snapshot → Prop) (id : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEp id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEp_sameSnapshot id).wp P

theorem getEpi_sameSnapshot (id : EpiId) : SameSnapshot (Leanux.getEpi id) := by
  frame_same [getEpi] using []

theorem getEpi_spec (P : Snapshot → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getEpi id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getEpi_sameSnapshot id).wp P

theorem setEpi_sameSnapshot (id : EpiId) (e : Epitem) : SameSnapshot (Leanux.setEpi id e) := by
  frame_same [setEpi] using []

theorem setEpi_spec (P : Snapshot → Prop) (id : EpiId) (e : Epitem) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setEpi id e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setEpi_sameSnapshot id e).wp P

theorem freeEpi_sameSnapshot (id : EpiId) : SameSnapshot (Leanux.freeEpi id) := by
  frame_same [freeEpi] using []

theorem freeEpi_spec (P : Snapshot → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEpi id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEpi_sameSnapshot id).wp P

theorem getPwq_sameSnapshot (id : PwqId) : SameSnapshot (Leanux.getPwq id) := by
  frame_same [getPwq] using []

theorem getPwq_spec (P : Snapshot → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPwq id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPwq_sameSnapshot id).wp P

theorem setPwq_sameSnapshot (id : PwqId) (p : EppollEntry) : SameSnapshot (Leanux.setPwq id p) := by
  frame_same [setPwq] using []

theorem setPwq_spec (P : Snapshot → Prop) (id : PwqId) (p : EppollEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setPwq id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPwq_sameSnapshot id p).wp P

theorem freePwq_sameSnapshot (id : PwqId) : SameSnapshot (Leanux.freePwq id) := by
  frame_same [freePwq] using []

theorem freePwq_spec (P : Snapshot → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freePwq id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freePwq_sameSnapshot id).wp P

/-! ## The heads and queueing -/

theorem getWaitQueue_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.getWaitQueue r) := by
  cases r <;> frame_same [getWaitQueue] using [getPipe_spec, getCtx_spec, getEp_spec]

theorem getWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getWaitQueue r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getWaitQueue_sameSnapshot r).wp P

theorem setWaitQueue_sameSnapshot (r : WaitQueueRef) (q : WaitQueue) : SameSnapshot (Leanux.setWaitQueue r q) := by
  cases r <;> frame_same [setWaitQueue] using [getPipe_spec, setPipe_spec, getCtx_spec, setCtx_spec,
    getEp_spec, setEp_spec]

theorem setWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) (q : WaitQueue) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setWaitQueue r q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setWaitQueue_sameSnapshot r q).wp P

theorem waitqueueActive_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.waitqueueActive r) := by
  frame_same [waitqueueActive] using [getWaitQueue_spec]

theorem waitqueueActive_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.waitqueueActive r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (waitqueueActive_sameSnapshot r).wp P

theorem addWaitQueue_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) : SameSnapshot (Leanux.addWaitQueue r e) := by
  frame_same [addWaitQueue] using [getWaitQueue_spec, setWaitQueue_spec]

theorem addWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.addWaitQueue r e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addWaitQueue_sameSnapshot r e).wp P

theorem addWaitQueueExclusive_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) :
    SameSnapshot (Leanux.addWaitQueueExclusive r e) := by
  frame_same [addWaitQueueExclusive] using [getWaitQueue_spec, setWaitQueue_spec]

theorem addWaitQueueExclusive_spec (P : Snapshot → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.addWaitQueueExclusive r e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addWaitQueueExclusive_sameSnapshot r e).wp P

theorem removeWaitQueue_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) :
    SameSnapshot (Leanux.removeWaitQueue r e) := by
  frame_same [removeWaitQueue] using [getWaitQueue_spec, setWaitQueue_spec]

theorem removeWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.removeWaitQueue r e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (removeWaitQueue_sameSnapshot r e).wp P

/-! ## The wake walk and its callback, by induction on the nesting fuel

At fuel `n + 1` the walk calls the entries at fuel `n`; the callback, the
safewake and the entry call at a given fuel chain through the walk at that
same fuel. So one induction: the walk at `0` makes no call, the walk at
`n + 1` uses the entry call at `n`, and the rest of each level follows. -/

/-- The three callers at one fuel, given the walk at that fuel. -/
theorem chain_of_common (fuel : Nat)
    (hcommon : ∀ (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) :
    (∀ (P : Snapshot → Prop) (ep : EpId) (epi : Option EpiId) (pollflags : UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollSafewakeAt fuel ep epi pollflags
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (pwq : PwqId) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollCallbackAt fuel pwq mode wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ e.callAt fuel mode wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) := by
  have safewake : ∀ ep epi pollflags, SameSnapshot (Leanux.epPollSafewakeAt fuel ep epi pollflags) := by
    intro ep epi pollflags
    frame_same [epPollSafewakeAt] using [hcommon]
  have safewake_spec := fun P ep epi pollflags => (safewake ep epi pollflags).wp P
  have callback : ∀ pwq mode wakeFlags key,
      SameSnapshot (Leanux.epPollCallbackAt fuel pwq mode wakeFlags key) := by
    intro pwq mode wakeFlags key
    frame_same [epPollCallbackAt] using [getPwq_spec, getEpi_spec, getEp_spec, setEp_spec,
      setEpi_spec, waitqueueActive_spec, safewake_spec]
  have callback_spec := fun P pwq mode wakeFlags key => (callback pwq mode wakeFlags key).wp P
  have call : ∀ (e : WaitEntry) mode wakeFlags key, SameSnapshot (e.callAt fuel mode wakeFlags key) := by
    intro e mode wakeFlags key
    obtain ⟨⟨pwq⟩, exclusive⟩ := e
    frame_same [WaitEntry.callAt] using [callback_spec]
  exact ⟨safewake_spec, callback_spec, fun P e mode wakeFlags key => (call e mode wakeFlags key).wp P⟩

/-- The walk at fuel `n + 1`, given the entry call at fuel `n`. -/
theorem common_succ (n : Nat)
    (hcall : ∀ (P : Snapshot → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ e.callAt n mode wakeFlags key ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpCommonAt (n + 1) r mode nrExclusive wakeFlags key) := by
  frame_same [wakeUpCommonAt] using [getWaitQueue_spec, hcall]

/-- The walk at fuel `0` makes no call. -/
theorem common_zero (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : SameSnapshot (Leanux.wakeUpCommonAt 0 r mode nrExclusive wakeFlags key) := by
  frame_same [wakeUpCommonAt] using [getWaitQueue_spec]

theorem wakeAt_specs (fuel : Nat) :
    (∀ (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ e.callAt fuel mode wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) := by
  induction fuel with
  | zero =>
    have common_spec := fun P r mode nrExclusive wakeFlags key =>
      (common_zero r mode nrExclusive wakeFlags key).wp P
    exact ⟨common_spec, (chain_of_common 0 common_spec).2.2⟩
  | succ n ih =>
    have common_spec := fun P r mode nrExclusive wakeFlags key =>
      (common_succ n ih.2 r mode nrExclusive wakeFlags key).wp P
    exact ⟨common_spec, (chain_of_common (n + 1) common_spec).2.2⟩

theorem wakeUpCommonAt_spec (P : Snapshot → Prop) (fuel : Nat) (r : WaitQueueRef) (mode : UInt32)
    (nrExclusive : Int) (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeAt_specs fuel).1 P r mode nrExclusive wakeFlags key

theorem epPollSafewakeAt_spec (P : Snapshot → Prop) (fuel : Nat) (ep : EpId) (epi : Option EpiId)
    (pollflags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollSafewakeAt fuel ep epi pollflags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (chain_of_common fuel ((wakeAt_specs fuel).1)).1 P ep epi pollflags

theorem epPollCallbackAt_spec (P : Snapshot → Prop) (fuel : Nat) (pwq : PwqId) (mode wakeFlags : UInt32)
    (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollCallbackAt fuel pwq mode wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (chain_of_common fuel ((wakeAt_specs fuel).1)).2.1 P pwq mode wakeFlags key

/-! ## The wakes at the top of a walk and the macros -/

theorem wakeUpCommon_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : SameSnapshot (Leanux.wakeUpCommon r mode nrExclusive wakeFlags key) := by
  frame_same [wakeUpCommon] using [wakeUpCommonAt_spec]

theorem wakeUpCommon_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommon r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpCommon_sameSnapshot r mode nrExclusive wakeFlags key).wp P

theorem epPollSafewake_sameSnapshot (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    SameSnapshot (Leanux.epPollSafewake ep epi pollflags) := by
  frame_same [epPollSafewake] using [epPollSafewakeAt_spec]

theorem epPollSafewake_spec (P : Snapshot → Prop) (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollSafewake ep epi pollflags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPollSafewake_sameSnapshot ep epi pollflags).wp P

theorem wakeUpCommonLock_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key) := by
  frame_same [wakeUpCommonLock] using [wakeUpCommon_spec]

theorem wakeUpCommonLock_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpCommonLock_sameSnapshot r mode nrExclusive wakeFlags key).wp P

theorem wakeUpBase_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpBase r mode nr key) := by
  frame_same [wakeUpBase] using [wakeUpCommonLock_spec]

theorem wakeUpBase_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpBase r mode nr key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpBase_sameSnapshot r mode nr key).wp P

theorem wakeUpLockedKey_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpLockedKey r mode key) := by
  frame_same [wakeUpLockedKey] using [wakeUpCommon_spec]

theorem wakeUpLockedKey_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpLockedKey r mode key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpLockedKey_sameSnapshot r mode key).wp P

theorem wakeUpSyncKey_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpSyncKey r mode key) := by
  frame_same [wakeUpSyncKey] using [wakeUpCommonLock_spec]

theorem wakeUpSyncKey_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpSyncKey r mode key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpSyncKey_sameSnapshot r mode key).wp P

theorem wakeUp_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUp r) := by
  frame_same [wakeUp] using [wakeUpBase_spec]

theorem wakeUp_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUp r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUp_sameSnapshot r).wp P

theorem wakeUpAll_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpAll r) := by
  frame_same [wakeUpAll] using [wakeUpBase_spec]

theorem wakeUpAll_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpAll r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpAll_sameSnapshot r).wp P

theorem wakeUpSync_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpSync r) := by
  frame_same [wakeUpSync] using [wakeUpSyncKey_spec]

theorem wakeUpSync_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpSync r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpSync_sameSnapshot r).wp P

theorem wakeUpInterruptible_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpInterruptible r) := by
  frame_same [wakeUpInterruptible] using [wakeUpBase_spec]

theorem wakeUpInterruptible_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptible r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptible_sameSnapshot r).wp P

theorem wakeUpInterruptibleAll_sameSnapshot (r : WaitQueueRef) :
    SameSnapshot (Leanux.wakeUpInterruptibleAll r) := by
  frame_same [wakeUpInterruptibleAll] using [wakeUpBase_spec]

theorem wakeUpInterruptibleAll_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptibleAll r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptibleAll_sameSnapshot r).wp P

theorem wakeUpPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) : SameSnapshot (Leanux.wakeUpPoll r m) := by
  frame_same [wakeUpPoll] using [wakeUpBase_spec]

theorem wakeUpPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpPoll_sameSnapshot r m).wp P

theorem wakeUpLockedPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) :
    SameSnapshot (Leanux.wakeUpLockedPoll r m) := by
  frame_same [wakeUpLockedPoll] using [wakeUpLockedKey_spec]

theorem wakeUpLockedPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpLockedPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpLockedPoll_sameSnapshot r m).wp P

theorem wakeUpInterruptibleSyncPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) :
    SameSnapshot (Leanux.wakeUpInterruptibleSyncPoll r m) := by
  frame_same [wakeUpInterruptibleSyncPoll] using [wakeUpSyncKey_spec]

theorem wakeUpInterruptibleSyncPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptibleSyncPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptibleSyncPoll_sameSnapshot r m).wp P

end Leanux.Proofs.WG.Keypairs.WaitFrames
