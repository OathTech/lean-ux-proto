import Leanux.Proofs.WG.Keypairs.Frames.FS
import Leanux.Proofs.WG.Keypairs.Frames.Eventpoll
import Leanux.FS.Eventpoll

/-! Receive-state framing for the epoll system calls (`Leanux/FS/Eventpoll.lean`,
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
  frame_same [epStartScan] using [getEp_spec, setEp_spec]

theorem epStartScan_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epStartScan ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epStartScan_sameSnapshot ep).wp P

theorem epDoneScan_sameSnapshot (ep : EpId) (batch : List EpiId) : SameSnapshot (Leanux.epDoneScan ep batch) := by
  frame_same [epDoneScan] using [getEp_spec, setEp_spec, getEpi_spec, setEpi_spec, waitqueueActive_spec]

theorem epDoneScan_spec (P : Snapshot → Prop) (ep : EpId) (batch : List EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epDoneScan ep batch
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epDoneScan_sameSnapshot ep batch).wp P

theorem epSetBusyPollNapiId_sameSnapshot (epiId : EpiId) : SameSnapshot (Leanux.epSetBusyPollNapiId epiId) := by
  frame_same [epSetBusyPollNapiId] using [getEp_spec, getEpi_spec]

theorem epSetBusyPollNapiId_spec (P : Snapshot → Prop) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epSetBusyPollNapiId epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epSetBusyPollNapiId_sameSnapshot epiId).wp P

theorem epAlloc_sameSnapshot : SameSnapshot Leanux.epAlloc := by
  frame_same [epAlloc] using [hiddenAlloc_snapshot_spec, refcountIncGuestWide_spec, setEp_spec]

theorem epAlloc_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAlloc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := epAlloc_sameSnapshot.wp P

theorem epGet_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epGet ep) := by
  frame_same [epGet] using [getEp_spec, setEp_spec, refcountInc_spec]

theorem epGet_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epGet ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epGet_sameSnapshot ep).wp P

/-! ## tfile_check_list -/

theorem listFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.listFile fid) := by
  frame_same [listFile] using [fileIncNotZero_spec]

theorem listFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.listFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listFile_sameSnapshot fid).wp P

theorem unlistFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.unlistFile fid) := by
  frame_same [unlistFile] using [getFile_spec, fEpItems_spec, freeEphead_spec, fput_spec]

theorem unlistFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.unlistFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (unlistFile_sameSnapshot fid).wp P

theorem clearTfileCheckList_sameSnapshot : SameSnapshot Leanux.clearTfileCheckList := by
  frame_same [clearTfileCheckList] using [unlistFile_spec]

theorem clearTfileCheckList_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.clearTfileCheckList
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := clearTfileCheckList_sameSnapshot.wp P

/-! ## The tree -/

theorem epFind_sameSnapshot (ep : EpId) (fid : FileId) (fd : Int) : SameSnapshot (Leanux.epFind ep fid fd) := by
  frame_same [epFind] using [getEp_spec, getEpi_spec]

theorem epFind_spec (P : Snapshot → Prop) (ep : EpId) (fid : FileId) (fd : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epFind ep fid fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epFind_sameSnapshot ep fid fd).wp P

theorem epRbtreeInsert_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRbtreeInsert ep epiId) := by
  frame_same [epRbtreeInsert] using [getEpi_spec, setEpi_spec, hiddenU64_spec, getEp_spec, setEp_spec]

theorem epRbtreeInsert_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRbtreeInsert ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRbtreeInsert_sameSnapshot ep epiId).wp P

/-! ## Reverse paths, by induction on the walk's fuel -/

theorem pathCountInc_sameSnapshot (nests : Nat) : SameSnapshot (Leanux.pathCountInc nests) := by
  frame_same [pathCountInc] using []

theorem pathCountInc_spec (P : Snapshot → Prop) (nests : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pathCountInc nests
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pathCountInc_sameSnapshot nests).wp P

theorem reversePathCheckProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (refs : List EpiId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.reversePathCheckProc fuel refs depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P refs depth
    have h : SameSnapshot (Leanux.reversePathCheckProc 0 refs depth) := by
      frame_same [reversePathCheckProc] using []
    exact h.wp P
  | succ n ih =>
    intro P refs depth
    have h : SameSnapshot (Leanux.reversePathCheckProc (n + 1) refs depth) := by
      frame_same [reversePathCheckProc] using [getEp_spec, getEpi_spec, pathCountInc_spec, ih]
    exact h.wp P

theorem reversePathCheck_sameSnapshot : SameSnapshot Leanux.reversePathCheck := by
  have proc_spec := reversePathCheckProc_spec (EP_MAX_NESTS + 2)
  frame_same [reversePathCheck] using [getFile_spec, fEpItems_spec, proc_spec]

theorem reversePathCheck_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.reversePathCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := reversePathCheck_sameSnapshot.wp P

/-! ## Attaching, allocating and registering an item -/

theorem epAttachFile_sameSnapshot (fid : FileId) (epiId : EpiId) : SameSnapshot (Leanux.epAttachFile fid epiId) := by
  frame_same [epAttachFile] using [getFile_spec, setFile_spec, epOf_spec, hiddenAlloc_snapshot_spec,
    getEp_spec, setEp_spec, freeEphead_spec]

theorem epAttachFile_spec (P : Snapshot → Prop) (fid : FileId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAttachFile fid epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epAttachFile_sameSnapshot fid epiId).wp P

theorem epAllocEpitem_sameSnapshot (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    SameSnapshot (Leanux.epAllocEpitem ep event tfile fd) := by
  frame_same [epAllocEpitem] using [hiddenAlloc_snapshot_spec, setEpi_spec]

theorem epAllocEpitem_spec (P : Snapshot → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epAllocEpitem ep event tfile fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epAllocEpitem_sameSnapshot ep event tfile fd).wp P

theorem epRegisterEpitem_sameSnapshot (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    SameSnapshot (Leanux.epRegisterEpitem ep epiId tep fullCheck) := by
  frame_same [epRegisterEpitem] using [getEpi_spec, epAttachFile_spec, freeEpi_spec, listFile_spec,
    epRbtreeInsert_spec, epGet_spec]

theorem epRegisterEpitem_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRegisterEpitem ep epiId tep fullCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRegisterEpitem_sameSnapshot ep epiId tep fullCheck).wp P

/-! ## The poll table and the `poll` operations -/

theorem epPtableQueueProc_sameSnapshot (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    SameSnapshot (Leanux.epPtableQueueProc file whead pt) := by
  frame_same [epPtableQueueProc] using [hiddenAlloc_snapshot_spec, setPwq_spec, getEpi_spec, setEpi_spec,
    addWaitQueue_spec, addWaitQueueExclusive_spec]

theorem epPtableQueueProc_spec (P : Snapshot → Prop) (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPtableQueueProc file whead pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPtableQueueProc_sameSnapshot file whead pt).wp P

theorem pollWait_sameSnapshot (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    SameSnapshot (Leanux.pollWait filp waitAddress p) := by
  frame_same [pollWait] using [epPtableQueueProc_spec]

theorem pollWait_spec (P : Snapshot → Prop) (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pollWait filp waitAddress p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pollWait_sameSnapshot filp waitAddress p).wp P

theorem eventfdPoll_sameSnapshot (fid : FileId) (wait : PollTable) : SameSnapshot (Leanux.eventfdPoll fid wait) := by
  frame_same [eventfdPoll] using [getFile_spec, eventfdCtxOf_spec, pollWait_spec, getCtx_spec]

theorem eventfdPoll_spec (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdPoll fid wait
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdPoll_sameSnapshot fid wait).wp P

theorem pipePoll_sameSnapshot (fid : FileId) (wait : PollTable) : SameSnapshot (Leanux.pipePoll fid wait) := by
  frame_same [pipePoll] using [getFile_spec, pipeOf_spec, getPipe_spec, setPipe_spec, pollWait_spec]

theorem pipePoll_spec (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipePoll fid wait
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipePoll_sameSnapshot fid wait).wp P

theorem fopPoll_sameSnapshot (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    SameSnapshot (Leanux.fopPoll fid pt which) := by
  cases which with
  | none => frame_same [Leanux.fopPoll] using [eventfdPoll_spec, pipePoll_spec]
  | some k => cases k <;> frame_same [Leanux.fopPoll] using [eventfdPoll_spec, pipePoll_spec]

theorem fopPoll_spec (P : Snapshot → Prop) (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopPoll fid pt which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopPoll_sameSnapshot fid pt which).wp P

theorem vfsPoll_sameSnapshot (fid : FileId) (pt : PollTable) : SameSnapshot (Leanux.vfsPoll fid pt) := by
  frame_same [vfsPoll] using [getFile_spec, fopsOf_spec, fopPoll_spec]

theorem vfsPoll_spec (P : Snapshot → Prop) (fid : FileId) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.vfsPoll fid pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (vfsPoll_sameSnapshot fid pt).wp P

/-! ## `ep_item_poll` and `__ep_eventpoll_poll`, by induction on the nesting fuel

`ep_item_poll` at fuel `n + 1` polls a nested set at fuel `n`, and that set's
poll calls `ep_item_poll` at the same fuel `n`. -/

theorem epItemPoll_zero (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPoll 0 epiId pt depth) := by
  frame_same [epItemPoll] using [getEpi_spec, fileIncNotZero_spec, getFile_spec, vfsPoll_spec, fput_spec]

theorem epItemPoll_succ (n : Nat)
    (hinner : ∀ (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollPollInner n fid wait depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPoll (n + 1) epiId pt depth) := by
  frame_same [epItemPoll] using [getEpi_spec, fileIncNotZero_spec, getFile_spec, vfsPoll_spec, fput_spec, hinner]

theorem epEventpollPollInner_of_item (fuel : Nat)
    (hitem : ∀ (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄)
    (fid : FileId) (wait : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epEventpollPollInner fuel fid wait depth) := by
  frame_same [epEventpollPollInner] using [getFile_spec, epOf_spec, pollWait_spec, epStartScan_spec,
    getEpi_spec, setEpi_spec, epDoneScan_spec, hitem]

theorem epPollAt_specs (fuel : Nat) :
    (∀ (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) ∧
    (∀ (P : Snapshot → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollPollInner fuel fid wait depth ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) := by
  induction fuel with
  | zero =>
    have item := fun P epiId pt depth => (epItemPoll_zero epiId pt depth).wp P
    exact ⟨item, fun P fid wait depth => (epEventpollPollInner_of_item 0 item fid wait depth).wp P⟩
  | succ n ih =>
    have item := fun P epiId pt depth => (epItemPoll_succ n ih.2 epiId pt depth).wp P
    exact ⟨item, fun P fid wait depth => (epEventpollPollInner_of_item (n + 1) item fid wait depth).wp P⟩

theorem epItemPoll_spec (P : Snapshot → Prop) (fuel : Nat) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPollAt_specs fuel).1 P epiId pt depth

theorem epItemPollAt_sameSnapshot (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameSnapshot (Leanux.epItemPollAt epiId pt depth) := by
  frame_same [epItemPollAt] using [epItemPoll_spec]

theorem epItemPollAt_spec (P : Snapshot → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epItemPollAt epiId pt depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epItemPollAt_sameSnapshot epiId pt depth).wp P

/-! ## Insertion, modification, delivery -/

theorem epInsert_sameSnapshot (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    SameSnapshot (Leanux.epInsert ep event tfile fd fullCheck) := by
  frame_same [epInsert] using [getFile_spec, epOf_spec, epAllocEpitem_spec, epRegisterEpitem_spec,
    reversePathCheck_spec, epRemove_spec, getEpi_spec, setEpi_spec, epItemPollAt_spec,
    epSetBusyPollNapiId_spec, getEp_spec, setEp_spec, waitqueueActive_spec, epPollSafewake_spec]

theorem epInsert_spec (P : Snapshot → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epInsert ep event tfile fd fullCheck
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epInsert_sameSnapshot ep event tfile fd fullCheck).wp P

theorem epModify_sameSnapshot (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    SameSnapshot (Leanux.epModify ep epiId event) := by
  frame_same [epModify] using [getEpi_spec, setEpi_spec, epItemPollAt_spec, getEp_spec, setEp_spec,
    waitqueueActive_spec, epPollSafewake_spec]

theorem epModify_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epModify ep epiId event
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epModify_sameSnapshot ep epiId event).wp P

theorem epollPutUevent_sameSnapshot (revents : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.epollPutUevent revents data) := by
  frame_same [epollPutUevent] using []

theorem epollPutUevent_spec (P : Snapshot → Prop) (revents : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epollPutUevent revents data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epollPutUevent_sameSnapshot revents data).wp P

theorem epDeliverEvent_sameSnapshot (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    SameSnapshot (Leanux.epDeliverEvent ep epiId pt) := by
  frame_same [epDeliverEvent] using [getEpi_spec, setEpi_spec, epItemPollAt_spec, epollPutUevent_spec,
    getEp_spec, setEp_spec]

theorem epDeliverEvent_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epDeliverEvent ep epiId pt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epDeliverEvent_sameSnapshot ep epiId pt).wp P

theorem epSendEvents_sameSnapshot (ep : EpId) (maxevents : Int) : SameSnapshot (Leanux.epSendEvents ep maxevents) := by
  frame_same [epSendEvents] using [epStartScan_spec, epDeliverEvent_spec, epDoneScan_spec]

theorem epSendEvents_spec (P : Snapshot → Prop) (ep : EpId) (maxevents : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epSendEvents ep maxevents
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epSendEvents_sameSnapshot ep maxevents).wp P

/-! ## Waiting -/

theorem epTimeoutToTimespec_sameSnapshot (ms : Int) : SameSnapshot (Leanux.epTimeoutToTimespec ms) := by
  frame_same [epTimeoutToTimespec] using []

theorem epTimeoutToTimespec_spec (P : Snapshot → Prop) (ms : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epTimeoutToTimespec ms
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epTimeoutToTimespec_sameSnapshot ms).wp P

theorem epEventsAvailable_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epEventsAvailable ep) := by
  frame_same [epEventsAvailable] using [getEp_spec]

theorem epEventsAvailable_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventsAvailable ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epEventsAvailable_sameSnapshot ep).wp P

theorem epPoll_sameSnapshot (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    SameSnapshot (Leanux.epPoll ep maxevents timeout) := by
  frame_same [epPoll] using [epEventsAvailable_spec, epSendEvents_spec]

theorem epPoll_spec (P : Snapshot → Prop) (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epPoll ep maxevents timeout
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epPoll_sameSnapshot ep maxevents timeout).wp P

theorem doEpollWait_sameSnapshot (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    SameSnapshot (Leanux.doEpollWait epfd maxevents to) := by
  frame_same [doEpollWait] using [fdget_spec, fdput_spec, getFile_spec, epOf_spec, epPoll_spec]

theorem doEpollWait_spec (P : Snapshot → Prop) (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollWait epfd maxevents to
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollWait_sameSnapshot epfd maxevents to).wp P

/-! ## Creation -/

theorem doEpollCreate_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.doEpollCreate flags) := by
  frame_same [doEpollCreate] using [epAlloc_spec, getUnusedFdFlags_spec, epClearAndPut_spec,
    anonInodeGetfile_spec, putUnusedFd_spec, getEp_spec, setEp_spec, fdInstall_spec]

theorem doEpollCreate_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollCreate flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCreate_sameSnapshot flags).wp P

/-! ## The loop checks, by induction on their fuel -/

theorem epollMutexLock_sameSnapshot (nonblock : Bool) : SameSnapshot (Leanux.epollMutexLock nonblock) := by
  frame_same [epollMutexLock] using []

theorem epollMutexLock_spec (P : Snapshot → Prop) (nonblock : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epollMutexLock nonblock
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epollMutexLock_sameSnapshot nonblock).wp P

theorem epLoopCheckProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epLoopCheckProc fuel ep depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P ep depth
    have h : SameSnapshot (Leanux.epLoopCheckProc 0 ep depth) := by
      frame_same [epLoopCheckProc] using []
    exact h.wp P
  | succ n ih =>
    intro P ep depth
    have h : SameSnapshot (Leanux.epLoopCheckProc (n + 1) ep depth) := by
      frame_same [epLoopCheckProc] using [getEp_spec, setEp_spec, getEpi_spec, getFile_spec, epOf_spec,
        listFile_spec, ih]
    exact h.wp P

theorem epGetUpwardsDepthProc_spec (fuel : Nat) : ∀ (P : Snapshot → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epGetUpwardsDepthProc fuel ep depth
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P ep depth
    have h : SameSnapshot (Leanux.epGetUpwardsDepthProc 0 ep depth) := by
      frame_same [epGetUpwardsDepthProc] using []
    exact h.wp P
  | succ n ih =>
    intro P ep depth
    have h : SameSnapshot (Leanux.epGetUpwardsDepthProc (n + 1) ep depth) := by
      frame_same [epGetUpwardsDepthProc] using [getEp_spec, setEp_spec, getEpi_spec, ih]
    exact h.wp P

theorem epLoopCheck_sameSnapshot (ep to : EpId) : SameSnapshot (Leanux.epLoopCheck ep to) := by
  have loop_spec := epLoopCheckProc_spec (EP_MAX_NESTS + 2)
  have up_spec := epGetUpwardsDepthProc_spec (EP_MAX_NESTS + 2)
  frame_same [epLoopCheck] using [loop_spec, up_spec]

theorem epLoopCheck_spec (P : Snapshot → Prop) (ep to : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epLoopCheck ep to
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epLoopCheck_sameSnapshot ep to).wp P

/-! ## ctl -/

theorem doEpollCtlBody_sameSnapshot (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot ((pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data) := by
  frame_same [_private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody] using [getFile_spec, fopsOf_spec,
    epOf_spec, epollMutexLock_spec, getEp_spec, epLoopCheck_spec, epFind_spec, epInsert_spec, epRemove_spec,
    getEpi_spec, epModify_spec]

theorem doEpollCtlBody_spec (P : Snapshot → Prop) (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCtlBody_sameSnapshot fId tId op fd events data).wp P

theorem doEpollCtl_sameSnapshot (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.doEpollCtl epfd op fd events data) := by
  frame_same [doEpollCtl] using [fdget_spec, fdput_spec, doEpollCtlBody_spec, clearTfileCheckList_spec]

theorem doEpollCtl_spec (P : Snapshot → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEpollCtl_sameSnapshot epfd op fd events data).wp P

/-! ## The system calls -/

theorem sysEpollCreate1_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.sysEpollCreate1 flags) := by
  frame_same [sysEpollCreate1] using [doEpollCreate_spec]

theorem sysEpollCreate1_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollCreate1 flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollCreate1_sameSnapshot flags).wp P

theorem sysEpollCtl_sameSnapshot (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameSnapshot (Leanux.sysEpollCtl epfd op fd events data) := by
  frame_same [sysEpollCtl] using [doEpollCtl_spec]

theorem sysEpollCtl_spec (P : Snapshot → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollCtl_sameSnapshot epfd op fd events data).wp P

theorem sysEpollWait_sameSnapshot (epfd : Nat) (maxevents timeout : Int) :
    SameSnapshot (Leanux.sysEpollWait epfd maxevents timeout) := by
  frame_same [sysEpollWait] using [epTimeoutToTimespec_spec, doEpollWait_spec]

theorem sysEpollWait_spec (P : Snapshot → Prop) (epfd : Nat) (maxevents timeout : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEpollWait epfd maxevents timeout
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEpollWait_sameSnapshot epfd maxevents timeout).wp P

end Leanux.Proofs.WG.Keypairs.EventpollFrames
