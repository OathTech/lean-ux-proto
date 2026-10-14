import Leanux.Proofs.WG.Keypairs.Frames.Kernel
import Leanux.Proofs.Framing.Wait
import Leanux.FS.Wait

/-! Compatibility receive-state framing for the wait-queue service (`Leanux/FS/Wait.lean`,
the epoll carry-over of 2026-10-13): the epoll stores, the heads, queueing,
and the wake walk with the callback it runs. The walk and the callback are
one mutual group bounded by a nesting fuel, so they are framed together by
induction on the fuel; nothing in the group touches the keypair store. -/
namespace Leanux.Proofs.WG.Keypairs.WaitFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames

/-! ## The epoll stores (`Leanux/Kernel/Defs.lean`) -/

theorem getEp_sameSnapshot (id : EpId) : SameSnapshot (Leanux.getEp id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.getEp_sameWGKernel

theorem getEp_spec (P : Snapshot → Prop) (id : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getEp id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getEp_sameSnapshot id).wp P

theorem setEp_sameSnapshot (id : EpId) (e : Eventpoll) : SameSnapshot (Leanux.setEp id e) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.setEp_sameWGKernel

theorem setEp_spec (P : Snapshot → Prop) (id : EpId) (e : Eventpoll) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setEp id e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setEp_sameSnapshot id e).wp P

theorem freeEp_sameSnapshot (id : EpId) : SameSnapshot (Leanux.freeEp id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.freeEp_sameWGKernel

theorem freeEp_spec (P : Snapshot → Prop) (id : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEp id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEp_sameSnapshot id).wp P

theorem getEpi_sameSnapshot (id : EpiId) : SameSnapshot (Leanux.getEpi id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.getEpi_sameWGKernel

theorem getEpi_spec (P : Snapshot → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getEpi id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getEpi_sameSnapshot id).wp P

theorem setEpi_sameSnapshot (id : EpiId) (e : Epitem) : SameSnapshot (Leanux.setEpi id e) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.setEpi_sameWGKernel

theorem setEpi_spec (P : Snapshot → Prop) (id : EpiId) (e : Epitem) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setEpi id e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setEpi_sameSnapshot id e).wp P

theorem freeEpi_sameSnapshot (id : EpiId) : SameSnapshot (Leanux.freeEpi id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.freeEpi_sameWGKernel

theorem freeEpi_spec (P : Snapshot → Prop) (id : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEpi id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEpi_sameSnapshot id).wp P

theorem getPwq_sameSnapshot (id : PwqId) : SameSnapshot (Leanux.getPwq id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.getPwq_sameWGKernel

theorem getPwq_spec (P : Snapshot → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPwq id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPwq_sameSnapshot id).wp P

theorem setPwq_sameSnapshot (id : PwqId) (p : EppollEntry) : SameSnapshot (Leanux.setPwq id p) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.setPwq_sameWGKernel

theorem setPwq_spec (P : Snapshot → Prop) (id : PwqId) (p : EppollEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setPwq id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPwq_sameSnapshot id p).wp P

theorem freePwq_sameSnapshot (id : PwqId) : SameSnapshot (Leanux.freePwq id) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.freePwq_sameWGKernel

theorem freePwq_spec (P : Snapshot → Prop) (id : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freePwq id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freePwq_sameSnapshot id).wp P

/-! ## The heads and queueing -/

theorem getWaitQueue_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.getWaitQueue r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.getWaitQueue_sameWGKernel

theorem getWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getWaitQueue r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getWaitQueue_sameSnapshot r).wp P

theorem setWaitQueue_sameSnapshot (r : WaitQueueRef) (q : WaitQueue) : SameSnapshot (Leanux.setWaitQueue r q) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.setWaitQueue_sameWGKernel

theorem setWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) (q : WaitQueue) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setWaitQueue r q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setWaitQueue_sameSnapshot r q).wp P

theorem waitqueueActive_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.waitqueueActive r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.waitqueueActive_sameWGKernel

theorem waitqueueActive_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.waitqueueActive r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (waitqueueActive_sameSnapshot r).wp P

theorem addWaitQueue_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) : SameSnapshot (Leanux.addWaitQueue r e) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.addWaitQueue_sameWGKernel

theorem addWaitQueue_spec (P : Snapshot → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.addWaitQueue r e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addWaitQueue_sameSnapshot r e).wp P

theorem addWaitQueueExclusive_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) :
    SameSnapshot (Leanux.addWaitQueueExclusive r e) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.addWaitQueueExclusive_sameWGKernel

theorem addWaitQueueExclusive_spec (P : Snapshot → Prop) (r : WaitQueueRef) (e : WaitEntry) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.addWaitQueueExclusive r e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addWaitQueueExclusive_sameSnapshot r e).wp P

theorem removeWaitQueue_sameSnapshot (r : WaitQueueRef) (e : WaitEntry) :
    SameSnapshot (Leanux.removeWaitQueue r e) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.removeWaitQueue_sameWGKernel

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
  have hs := Framing.WaitFrames.chain_of_common fuel (Framing.WaitFrames.wakeAt_specs fuel).1
  refine ⟨?_, ?_, ?_⟩
  · intro P ep epi pollflags
    exact hs.1 (fun v => P (snapshotOfWGKernelView v)) ep epi pollflags
  · intro P pwq mode wakeFlags key
    exact hs.2.1 (fun v => P (snapshotOfWGKernelView v)) pwq mode wakeFlags key
  · intro P e mode wakeFlags key
    exact hs.2.2 (fun v => P (snapshotOfWGKernelView v)) e mode wakeFlags key

/-- The walk at fuel `n + 1`, given the entry call at fuel `n`. -/
theorem common_succ (n : Nat)
    (hcall : ∀ (P : Snapshot → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ e.callAt n mode wakeFlags key ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpCommonAt (n + 1) r mode nrExclusive wakeFlags key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.SameView.of_wp
  intro initial
  exact (Framing.WaitFrames.wakeAt_specs (n + 1)).1 (fun v => v = initial) r mode nrExclusive wakeFlags key

/-- The walk at fuel `0` makes no call. -/
theorem common_zero (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : SameSnapshot (Leanux.wakeUpCommonAt 0 r mode nrExclusive wakeFlags key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.common_zero

theorem wakeAt_specs (fuel : Nat) :
    (∀ (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonAt fuel r mode nrExclusive wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ e.callAt fuel mode wakeFlags key
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) := by
  constructor
  · intro P r mode nrExclusive wakeFlags key
    exact (Framing.WaitFrames.wakeAt_specs fuel).1 (fun v => P (snapshotOfWGKernelView v)) r mode nrExclusive wakeFlags key
  · intro P e mode wakeFlags key
    exact (Framing.WaitFrames.wakeAt_specs fuel).2 (fun v => P (snapshotOfWGKernelView v)) e mode wakeFlags key

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
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpCommon_sameWGKernel

theorem wakeUpCommon_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommon r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpCommon_sameSnapshot r mode nrExclusive wakeFlags key).wp P

theorem epPollSafewake_sameSnapshot (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    SameSnapshot (Leanux.epPollSafewake ep epi pollflags) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.epPollSafewake_sameWGKernel

theorem epPollSafewake_spec (P : Snapshot → Prop) (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPollSafewake ep epi pollflags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPollSafewake_sameSnapshot ep epi pollflags).wp P

theorem wakeUpCommonLock_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpCommonLock_sameWGKernel

theorem wakeUpCommonLock_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
    (wakeFlags : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpCommonLock r mode nrExclusive wakeFlags key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpCommonLock_sameSnapshot r mode nrExclusive wakeFlags key).wp P

theorem wakeUpBase_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpBase r mode nr key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpBase_sameWGKernel

theorem wakeUpBase_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpBase r mode nr key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpBase_sameSnapshot r mode nr key).wp P

theorem wakeUpLockedKey_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpLockedKey r mode key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpLockedKey_sameWGKernel

theorem wakeUpLockedKey_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpLockedKey r mode key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpLockedKey_sameSnapshot r mode key).wp P

theorem wakeUpSyncKey_sameSnapshot (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    SameSnapshot (Leanux.wakeUpSyncKey r mode key) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpSyncKey_sameWGKernel

theorem wakeUpSyncKey_spec (P : Snapshot → Prop) (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpSyncKey r mode key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpSyncKey_sameSnapshot r mode key).wp P

theorem wakeUp_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUp r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUp_sameWGKernel

theorem wakeUp_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUp r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUp_sameSnapshot r).wp P

theorem wakeUpAll_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpAll r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpAll_sameWGKernel

theorem wakeUpAll_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpAll r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpAll_sameSnapshot r).wp P

theorem wakeUpSync_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpSync r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpSync_sameWGKernel

theorem wakeUpSync_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpSync r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpSync_sameSnapshot r).wp P

theorem wakeUpInterruptible_sameSnapshot (r : WaitQueueRef) : SameSnapshot (Leanux.wakeUpInterruptible r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpInterruptible_sameWGKernel

theorem wakeUpInterruptible_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptible r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptible_sameSnapshot r).wp P

theorem wakeUpInterruptibleAll_sameSnapshot (r : WaitQueueRef) :
    SameSnapshot (Leanux.wakeUpInterruptibleAll r) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpInterruptibleAll_sameWGKernel

theorem wakeUpInterruptibleAll_spec (P : Snapshot → Prop) (r : WaitQueueRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptibleAll r
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptibleAll_sameSnapshot r).wp P

theorem wakeUpPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) : SameSnapshot (Leanux.wakeUpPoll r m) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpPoll_sameWGKernel

theorem wakeUpPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpPoll_sameSnapshot r m).wp P

theorem wakeUpLockedPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) :
    SameSnapshot (Leanux.wakeUpLockedPoll r m) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpLockedPoll_sameWGKernel

theorem wakeUpLockedPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpLockedPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpLockedPoll_sameSnapshot r m).wp P

theorem wakeUpInterruptibleSyncPoll_sameSnapshot (r : WaitQueueRef) (m : UInt32) :
    SameSnapshot (Leanux.wakeUpInterruptibleSyncPoll r m) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.WaitFrames.wakeUpInterruptibleSyncPoll_sameWGKernel

theorem wakeUpInterruptibleSyncPoll_spec (P : Snapshot → Prop) (r : WaitQueueRef) (m : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.wakeUpInterruptibleSyncPoll r m
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wakeUpInterruptibleSyncPoll_sameSnapshot r m).wp P

end Leanux.Proofs.WG.Keypairs.WaitFrames
