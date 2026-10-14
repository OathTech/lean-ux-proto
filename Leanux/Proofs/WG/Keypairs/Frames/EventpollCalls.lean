import Leanux.Proofs.Framing.EventpollCalls
import Leanux.Proofs.WG.Keypairs.Frames.FS
import Leanux.Proofs.WG.Keypairs.Frames.Eventpoll
import Leanux.FS.Eventpoll

/-! Compatibility receive-state framing for the epoll system calls (`Leanux/FS/Eventpoll.lean`,
`Poll.lean`, the `poll` operations of pipes and eventfds): create, ctl and
wait, with the three bounded recursions of the mirror framed by induction on
their fuel in the pattern of `Frames/Wait.lean`: the reverse-path walk, the
loop-check and upwards-depth walks, and `ep_item_poll` with
`__ep_eventpoll_poll`. An epoll call never touches the keypair store, so every
contract is the projection unchanged. -/
namespace Leanux.Proofs.WG.Keypairs.EventpollFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux.Proofs.WG.Keypairs.FSFrames Leanux.Proofs.WG.Keypairs.PipeAux
open Leanux.Proofs.WG.Keypairs.WaitFrames Leanux.Proofs.WG.Keypairs.PipeFrames

set_option maxHeartbeats 1000000

/-! ## Scans, the busy-poll stub, allocation, references -/

theorem epStartScan_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epStartScan ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epStartScan_sameWGKernel

theorem epStartScan_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epStartScan ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epStartScan_sameSnapshot ep).wp P

theorem epDoneScan_sameSnapshot (ep : EpId) (batch : List EpiId) : SameSnapshot (Leanux.epDoneScan ep batch) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epDoneScan_sameWGKernel

theorem epDoneScan_spec (P : Snapshot → Prop) (ep : EpId) (batch : List EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epDoneScan ep batch
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epDoneScan_sameSnapshot ep batch).wp P

theorem epSetBusyPollNapiId_sameSnapshot (epiId : EpiId) : SameSnapshot (Leanux.epSetBusyPollNapiId epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epSetBusyPollNapiId_sameWGKernel

theorem epSetBusyPollNapiId_spec (P : Snapshot → Prop) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epSetBusyPollNapiId epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epSetBusyPollNapiId_sameSnapshot epiId).wp P

theorem epAlloc_sameSnapshot : SameSnapshot Leanux.epAlloc := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epAlloc_sameWGKernel

theorem epAlloc_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAlloc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := epAlloc_sameSnapshot.wp P

theorem epGet_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epGet ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epGet_sameWGKernel

theorem epGet_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epGet ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epGet_sameSnapshot ep).wp P

/-! ## tfile_check_list -/

theorem listFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.listFile fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.listFile_sameWGKernel

theorem listFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.listFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listFile_sameSnapshot fid).wp P

theorem unlistFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.unlistFile fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.unlistFile_sameWGKernel

theorem unlistFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.unlistFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (unlistFile_sameSnapshot fid).wp P

theorem clearTfileCheckList_sameSnapshot : SameSnapshot Leanux.clearTfileCheckList := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.clearTfileCheckList_sameWGKernel

theorem clearTfileCheckList_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.clearTfileCheckList
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := clearTfileCheckList_sameSnapshot.wp P

/-! ## The tree -/

theorem epFind_sameSnapshot (ep : EpId) (fid : FileId) (fd : Int) : SameSnapshot (Leanux.epFind ep fid fd) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epFind_sameWGKernel

theorem epFind_spec (P : Snapshot → Prop) (ep : EpId) (fid : FileId) (fd : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epFind ep fid fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epFind_sameSnapshot ep fid fd).wp P

theorem epRbtreeInsert_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRbtreeInsert ep epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRbtreeInsert_sameWGKernel

theorem epRbtreeInsert_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRbtreeInsert ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRbtreeInsert_sameSnapshot ep epiId).wp P

/-! ## Reverse paths, by induction on the walk's fuel -/

theorem pathCountInc_sameSnapshot (nests : Nat) : SameSnapshot (Leanux.pathCountInc nests) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.pathCountInc_sameWGKernel

theorem pathCountInc_spec (P : Snapshot → Prop) (nests : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pathCountInc nests
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pathCountInc_sameSnapshot nests).wp P

theorem reversePathCheckProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (refs : List EpiId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.reversePathCheckProc fuel refs depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  intro P a b
  exact Framing.EventpollFrames.reversePathCheckProc_spec fuel (fun v => P (snapshotOfWGKernelView v)) a b

theorem reversePathCheck_sameSnapshot : SameSnapshot Leanux.reversePathCheck := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.reversePathCheck_sameWGKernel

theorem reversePathCheck_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.reversePathCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := reversePathCheck_sameSnapshot.wp P

/-! ## Attaching, allocating and registering an item -/

theorem epAttachFile_sameSnapshot (fid : FileId) (epiId : EpiId) : SameSnapshot (Leanux.epAttachFile fid epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epAttachFile_sameWGKernel

theorem epAttachFile_spec (P : Snapshot → Prop) (fid : FileId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAttachFile fid epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epAttachFile_sameSnapshot fid epiId).wp P

theorem epAllocEpitem_sameSnapshot (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    SameSnapshot (Leanux.epAllocEpitem ep event tfile fd) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epAllocEpitem_sameWGKernel

theorem epAllocEpitem_spec (P : Snapshot → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAllocEpitem ep event tfile fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epAllocEpitem_sameSnapshot ep event tfile fd).wp P

theorem epRegisterEpitem_sameSnapshot (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    SameSnapshot (Leanux.epRegisterEpitem ep epiId tep fullCheck) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRegisterEpitem_sameWGKernel

theorem epRegisterEpitem_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRegisterEpitem ep epiId tep fullCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRegisterEpitem_sameSnapshot ep epiId tep fullCheck).wp P

/-! ## The poll table and the `poll` operations -/

theorem epPtableQueueProc_sameSnapshot (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    SameSnapshot (Leanux.epPtableQueueProc file whead pt) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epPtableQueueProc_sameWGKernel

theorem epPtableQueueProc_spec (P : Snapshot → Prop) (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPtableQueueProc file whead pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPtableQueueProc_sameSnapshot file whead pt).wp P

theorem pollWait_sameSnapshot (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    SameSnapshot (Leanux.pollWait filp waitAddress p) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.pollWait_sameWGKernel

theorem pollWait_spec (P : Snapshot → Prop) (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pollWait filp waitAddress p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pollWait_sameSnapshot filp waitAddress p).wp P

theorem eventfdPoll_sameSnapshot (fid : FileId) (wait : PollTable) : SameSnapshot (Leanux.eventfdPoll fid wait) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.eventfdPoll_sameWGKernel

theorem eventfdPoll_spec (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdPoll fid wait
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdPoll_sameSnapshot fid wait).wp P

theorem pipePoll_sameSnapshot (fid : FileId) (wait : PollTable) : SameSnapshot (Leanux.pipePoll fid wait) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.pipePoll_sameWGKernel

theorem pipePoll_spec (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipePoll fid wait
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipePoll_sameSnapshot fid wait).wp P

theorem fopPoll_sameSnapshot (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    SameSnapshot (Leanux.fopPoll fid pt which) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.fopPoll_sameWGKernel

theorem fopPoll_spec (P : Snapshot → Prop) (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopPoll fid pt which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopPoll_sameSnapshot fid pt which).wp P

theorem vfsPoll_sameSnapshot (fid : FileId) (pt : PollTable) : SameSnapshot (Leanux.vfsPoll fid pt) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.vfsPoll_sameWGKernel

theorem vfsPoll_spec (P : Snapshot → Prop) (fid : FileId) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.vfsPoll fid pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (vfsPoll_sameSnapshot fid pt).wp P

/-! ## `ep_item_poll` and `__ep_eventpoll_poll`, by induction on the nesting fuel

`ep_item_poll` at fuel `n + 1` polls a nested set at fuel `n`, and that set's
poll calls `ep_item_poll` at the same fuel `n`. -/

theorem epItemPoll_zero (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPoll 0 epiId pt depth) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epItemPoll_zero

theorem epItemPoll_succ (n : Nat)
    (hinner : ∀ (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollPollInner n fid wait depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPoll (n + 1) epiId pt depth) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.SameView.of_wp
  intro initial
  exact (Framing.EventpollFrames.epPollAt_specs (n + 1)).1 (fun v => v = initial) epiId pt depth

theorem epEventpollPollInner_of_item (fuel : Nat)
    (hitem : ∀ (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (fid : FileId) (wait : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epEventpollPollInner fuel fid wait depth) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.SameView.of_wp
  intro initial
  exact (Framing.EventpollFrames.epPollAt_specs fuel).2 (fun v => v = initial) fid wait depth

theorem epPollAt_specs (fuel : Nat) :
    (∀ (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollPollInner fuel fid wait depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) := by
  constructor
  · intro P epiId pt depth
    exact (Framing.EventpollFrames.epPollAt_specs fuel).1 (fun v => P (snapshotOfWGKernelView v)) epiId pt depth
  · intro P fid wait depth
    exact (Framing.EventpollFrames.epPollAt_specs fuel).2 (fun v => P (snapshotOfWGKernelView v)) fid wait depth

theorem epItemPoll_spec (P : Snapshot → Prop) (fuel : Nat) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPollAt_specs fuel).1 P epiId pt depth

theorem epItemPollAt_sameSnapshot (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPollAt epiId pt depth) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epItemPollAt_sameWGKernel

theorem epItemPollAt_spec (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPollAt epiId pt depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epItemPollAt_sameSnapshot epiId pt depth).wp P

/-! ## Insertion, modification, delivery -/

theorem epInsert_sameSnapshot (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    SameSnapshot (Leanux.epInsert ep event tfile fd fullCheck) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epInsert_sameWGKernel

theorem epInsert_spec (P : Snapshot → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epInsert ep event tfile fd fullCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epInsert_sameSnapshot ep event tfile fd fullCheck).wp P

theorem epModify_sameSnapshot (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    SameSnapshot (Leanux.epModify ep epiId event) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epModify_sameWGKernel

theorem epModify_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epModify ep epiId event
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epModify_sameSnapshot ep epiId event).wp P

theorem epollPutUevent_sameSnapshot (revents : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.epollPutUevent revents data) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epollPutUevent_sameWGKernel

theorem epollPutUevent_spec (P : Snapshot → Prop) (revents : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epollPutUevent revents data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epollPutUevent_sameSnapshot revents data).wp P

theorem epDeliverEvent_sameSnapshot (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    SameSnapshot (Leanux.epDeliverEvent ep epiId pt) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epDeliverEvent_sameWGKernel

theorem epDeliverEvent_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epDeliverEvent ep epiId pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epDeliverEvent_sameSnapshot ep epiId pt).wp P

theorem epSendEvents_sameSnapshot (ep : EpId) (maxevents : Int) : SameSnapshot (Leanux.epSendEvents ep maxevents) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epSendEvents_sameWGKernel

theorem epSendEvents_spec (P : Snapshot → Prop) (ep : EpId) (maxevents : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epSendEvents ep maxevents
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epSendEvents_sameSnapshot ep maxevents).wp P

/-! ## Waiting -/

theorem epTimeoutToTimespec_sameSnapshot (ms : Int) : SameSnapshot (Leanux.epTimeoutToTimespec ms) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epTimeoutToTimespec_sameWGKernel

theorem epTimeoutToTimespec_spec (P : Snapshot → Prop) (ms : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epTimeoutToTimespec ms
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epTimeoutToTimespec_sameSnapshot ms).wp P

theorem epEventsAvailable_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epEventsAvailable ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epEventsAvailable_sameWGKernel

theorem epEventsAvailable_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventsAvailable ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epEventsAvailable_sameSnapshot ep).wp P

theorem epPoll_sameSnapshot (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    SameSnapshot (Leanux.epPoll ep maxevents timeout) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epPoll_sameWGKernel

theorem epPoll_spec (P : Snapshot → Prop) (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPoll ep maxevents timeout
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPoll_sameSnapshot ep maxevents timeout).wp P

theorem doEpollWait_sameSnapshot (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    SameSnapshot (Leanux.doEpollWait epfd maxevents to) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.doEpollWait_sameWGKernel

theorem doEpollWait_spec (P : Snapshot → Prop) (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollWait epfd maxevents to
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollWait_sameSnapshot epfd maxevents to).wp P

/-! ## Creation -/

theorem doEpollCreate_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.doEpollCreate flags) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.doEpollCreate_sameWGKernel

theorem doEpollCreate_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollCreate flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCreate_sameSnapshot flags).wp P

/-! ## The loop checks, by induction on their fuel -/

theorem epollMutexLock_sameSnapshot (nonblock : Bool) : SameSnapshot (Leanux.epollMutexLock nonblock) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epollMutexLock_sameWGKernel

theorem epollMutexLock_spec (P : Snapshot → Prop) (nonblock : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epollMutexLock nonblock
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epollMutexLock_sameSnapshot nonblock).wp P

theorem epLoopCheckProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epLoopCheckProc fuel ep depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  intro P a b
  exact Framing.EventpollFrames.epLoopCheckProc_spec fuel (fun v => P (snapshotOfWGKernelView v)) a b

theorem epGetUpwardsDepthProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epGetUpwardsDepthProc fuel ep depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  intro P a b
  exact Framing.EventpollFrames.epGetUpwardsDepthProc_spec fuel (fun v => P (snapshotOfWGKernelView v)) a b

theorem epLoopCheck_sameSnapshot (ep to : EpId) : SameSnapshot (Leanux.epLoopCheck ep to) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epLoopCheck_sameWGKernel

theorem epLoopCheck_spec (P : Snapshot → Prop) (ep to : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epLoopCheck ep to
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epLoopCheck_sameSnapshot ep to).wp P

/-! ## ctl -/

theorem doEpollCtlBody_sameSnapshot (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot ((pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.doEpollCtlBody_sameWGKernel

theorem doEpollCtlBody_spec (P : Snapshot → Prop) (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCtlBody_sameSnapshot fId tId op fd events data).wp P

theorem doEpollCtl_sameSnapshot (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.doEpollCtl epfd op fd events data) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.doEpollCtl_sameWGKernel

theorem doEpollCtl_spec (P : Snapshot → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCtl_sameSnapshot epfd op fd events data).wp P

/-! ## The system calls -/

theorem sysEpollCreate1_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.sysEpollCreate1 flags) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.sysEpollCreate1_sameWGKernel

theorem sysEpollCreate1_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollCreate1 flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollCreate1_sameSnapshot flags).wp P

theorem sysEpollCtl_sameSnapshot (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.sysEpollCtl epfd op fd events data) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.sysEpollCtl_sameWGKernel

theorem sysEpollCtl_spec (P : Snapshot → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollCtl_sameSnapshot epfd op fd events data).wp P

theorem sysEpollWait_sameSnapshot (epfd : Nat) (maxevents timeout : Int) :
    SameSnapshot (Leanux.sysEpollWait epfd maxevents timeout) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.sysEpollWait_sameWGKernel

theorem sysEpollWait_spec (P : Snapshot → Prop) (epfd : Nat) (maxevents timeout : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollWait epfd maxevents timeout
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollWait_sameSnapshot epfd maxevents timeout).wp P

end Leanux.Proofs.WG.Keypairs.EventpollFrames
