import Leanux.Proofs.Framing.FS
import Leanux.Proofs.Framing.Eventpoll
import Leanux.FS.Eventpoll

/-! Full WireGuard kernel framing for the epoll system calls (`Leanux/FS/Eventpoll.lean`,
`Poll.lean`, the `poll` operations of pipes and eventfds): create, ctl and
wait, with the three bounded recursions of the mirror framed by induction on
their fuel in the pattern of `Frames/Wait.lean`: the reverse-path walk, the
loop-check and upwards-depth walks, and `ep_item_poll` with
`__ep_eventpoll_poll`. These original epoll paths retain the full WireGuard kernel view on normal return.
No successful-return or valid-input premise is imposed on their arguments. -/
namespace Leanux.Proofs.Framing.EventpollFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames
open Leanux.Proofs.Framing.FSFrames Leanux.Proofs.Framing.PipeAux
open Leanux.Proofs.Framing.WaitFrames Leanux.Proofs.Framing.PipeFrames

set_option maxHeartbeats 1000000

/-! ## Scans, the busy-poll stub, allocation, references -/

theorem epStartScan_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epStartScan ep) := by
  frame_wg [epStartScan] using [getEp_spec, setEp_spec]

theorem epStartScan_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epStartScan ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epStartScan_sameWGKernel ep).wp P

theorem epDoneScan_sameWGKernel (ep : EpId) (batch : List EpiId) : SameWGKernel (Leanux.epDoneScan ep batch) := by
  frame_wg [epDoneScan] using [getEp_spec, setEp_spec, getEpi_spec, setEpi_spec, waitqueueActive_spec]

theorem epDoneScan_spec (P : WGKernelView → Prop) (ep : EpId) (batch : List EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epDoneScan ep batch
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epDoneScan_sameWGKernel ep batch).wp P

theorem epSetBusyPollNapiId_sameWGKernel (epiId : EpiId) : SameWGKernel (Leanux.epSetBusyPollNapiId epiId) := by
  frame_wg [epSetBusyPollNapiId] using [getEp_spec, getEpi_spec]

theorem epSetBusyPollNapiId_spec (P : WGKernelView → Prop) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epSetBusyPollNapiId epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epSetBusyPollNapiId_sameWGKernel epiId).wp P

theorem epAlloc_sameWGKernel : SameWGKernel Leanux.epAlloc := by
  frame_wg [epAlloc] using [hiddenAlloc_spec, refcountIncGuestWide_spec, setEp_spec]

theorem epAlloc_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epAlloc
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := epAlloc_sameWGKernel.wp P

theorem epGet_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epGet ep) := by
  frame_wg [epGet] using [getEp_spec, setEp_spec, refcountInc_spec]

theorem epGet_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epGet ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epGet_sameWGKernel ep).wp P

/-! ## tfile_check_list -/

theorem listFile_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.listFile fid) := by
  frame_wg [listFile] using [fileIncNotZero_spec]

theorem listFile_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.listFile fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (listFile_sameWGKernel fid).wp P

theorem unlistFile_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.unlistFile fid) := by
  frame_wg [unlistFile] using [getFile_spec, fEpItems_spec, freeEphead_spec, fput_spec]

theorem unlistFile_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.unlistFile fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (unlistFile_sameWGKernel fid).wp P

theorem clearTfileCheckList_sameWGKernel : SameWGKernel Leanux.clearTfileCheckList := by
  frame_wg [clearTfileCheckList] using [unlistFile_spec]

theorem clearTfileCheckList_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.clearTfileCheckList
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := clearTfileCheckList_sameWGKernel.wp P

/-! ## The tree -/

theorem epFind_sameWGKernel (ep : EpId) (fid : FileId) (fd : Int) : SameWGKernel (Leanux.epFind ep fid fd) := by
  frame_wg [epFind] using [getEp_spec, getEpi_spec]

theorem epFind_spec (P : WGKernelView → Prop) (ep : EpId) (fid : FileId) (fd : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epFind ep fid fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epFind_sameWGKernel ep fid fd).wp P

theorem epRbtreeInsert_sameWGKernel (ep : EpId) (epiId : EpiId) : SameWGKernel (Leanux.epRbtreeInsert ep epiId) := by
  frame_wg [epRbtreeInsert] using [getEpi_spec, setEpi_spec, hiddenU64_spec, getEp_spec, setEp_spec]

theorem epRbtreeInsert_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRbtreeInsert ep epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRbtreeInsert_sameWGKernel ep epiId).wp P

/-! ## Reverse paths, by induction on the walk's fuel -/

theorem pathCountInc_sameWGKernel (nests : Nat) : SameWGKernel (Leanux.pathCountInc nests) := by
  frame_wg [pathCountInc] using []

theorem pathCountInc_spec (P : WGKernelView → Prop) (nests : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pathCountInc nests
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pathCountInc_sameWGKernel nests).wp P

theorem reversePathCheckProc_spec (fuel : Nat) : ∀ (P : WGKernelView → Prop) (refs : List EpiId) (depth : Nat),
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.reversePathCheckProc fuel refs depth
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P refs depth
    have h : SameWGKernel (Leanux.reversePathCheckProc 0 refs depth) := by
      frame_wg [reversePathCheckProc] using []
    exact h.wp P
  | succ n ih =>
    intro P refs depth
    have h : SameWGKernel (Leanux.reversePathCheckProc (n + 1) refs depth) := by
      frame_wg [reversePathCheckProc] using [getEp_spec, getEpi_spec, pathCountInc_spec, ih]
    exact h.wp P

theorem reversePathCheck_sameWGKernel : SameWGKernel Leanux.reversePathCheck := by
  have proc_spec := reversePathCheckProc_spec (EP_MAX_NESTS + 2)
  frame_wg [reversePathCheck] using [getFile_spec, fEpItems_spec, proc_spec]

theorem reversePathCheck_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.reversePathCheck
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := reversePathCheck_sameWGKernel.wp P

/-! ## Attaching, allocating and registering an item -/

theorem epAttachFile_sameWGKernel (fid : FileId) (epiId : EpiId) : SameWGKernel (Leanux.epAttachFile fid epiId) := by
  frame_wg [epAttachFile] using [getFile_spec, setFile_spec, epOf_spec, hiddenAlloc_spec,
    getEp_spec, setEp_spec, freeEphead_spec]

theorem epAttachFile_spec (P : WGKernelView → Prop) (fid : FileId) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epAttachFile fid epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epAttachFile_sameWGKernel fid epiId).wp P

theorem epAllocEpitem_sameWGKernel (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    SameWGKernel (Leanux.epAllocEpitem ep event tfile fd) := by
  frame_wg [epAllocEpitem] using [hiddenAlloc_spec, setEpi_spec]

theorem epAllocEpitem_spec (P : WGKernelView → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epAllocEpitem ep event tfile fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epAllocEpitem_sameWGKernel ep event tfile fd).wp P

theorem epRegisterEpitem_sameWGKernel (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    SameWGKernel (Leanux.epRegisterEpitem ep epiId tep fullCheck) := by
  frame_wg [epRegisterEpitem] using [getEpi_spec, epAttachFile_spec, freeEpi_spec, listFile_spec,
    epRbtreeInsert_spec, epGet_spec]

theorem epRegisterEpitem_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRegisterEpitem ep epiId tep fullCheck
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRegisterEpitem_sameWGKernel ep epiId tep fullCheck).wp P

/-! ## The poll table and the `poll` operations -/

theorem epPtableQueueProc_sameWGKernel (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    SameWGKernel (Leanux.epPtableQueueProc file whead pt) := by
  frame_wg [epPtableQueueProc] using [hiddenAlloc_spec, setPwq_spec, getEpi_spec, setEpi_spec,
    addWaitQueue_spec, addWaitQueueExclusive_spec]

theorem epPtableQueueProc_spec (P : WGKernelView → Prop) (file : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPtableQueueProc file whead pt
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epPtableQueueProc_sameWGKernel file whead pt).wp P

theorem pollWait_sameWGKernel (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    SameWGKernel (Leanux.pollWait filp waitAddress p) := by
  frame_wg [pollWait] using [epPtableQueueProc_spec]

theorem pollWait_spec (P : WGKernelView → Prop) (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pollWait filp waitAddress p
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pollWait_sameWGKernel filp waitAddress p).wp P

theorem eventfdPoll_sameWGKernel (fid : FileId) (wait : PollTable) : SameWGKernel (Leanux.eventfdPoll fid wait) := by
  frame_wg [eventfdPoll] using [getFile_spec, eventfdCtxOf_spec, pollWait_spec, getCtx_spec]

theorem eventfdPoll_spec (P : WGKernelView → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdPoll fid wait
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdPoll_sameWGKernel fid wait).wp P

theorem pipePoll_sameWGKernel (fid : FileId) (wait : PollTable) : SameWGKernel (Leanux.pipePoll fid wait) := by
  frame_wg [pipePoll] using [getFile_spec, pipeOf_spec, getPipe_spec, setPipe_spec, pollWait_spec]

theorem pipePoll_spec (P : WGKernelView → Prop) (fid : FileId) (wait : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipePoll fid wait
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipePoll_sameWGKernel fid wait).wp P

theorem fopPoll_sameWGKernel (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    SameWGKernel (Leanux.fopPoll fid pt which) := by
  cases which with
  | none => frame_wg [Leanux.fopPoll] using [eventfdPoll_spec, pipePoll_spec]
  | some k => cases k <;> frame_wg [Leanux.fopPoll] using [eventfdPoll_spec, pipePoll_spec]

theorem fopPoll_spec (P : WGKernelView → Prop) (fid : FileId) (pt : PollTable) (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopPoll fid pt which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopPoll_sameWGKernel fid pt which).wp P

theorem vfsPoll_sameWGKernel (fid : FileId) (pt : PollTable) : SameWGKernel (Leanux.vfsPoll fid pt) := by
  frame_wg [vfsPoll] using [getFile_spec, fopsOf_spec, fopPoll_spec]

theorem vfsPoll_spec (P : WGKernelView → Prop) (fid : FileId) (pt : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.vfsPoll fid pt
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (vfsPoll_sameWGKernel fid pt).wp P

/-! ## `ep_item_poll` and `__ep_eventpoll_poll`, by induction on the nesting fuel

`ep_item_poll` at fuel `n + 1` polls a nested set at fuel `n`, and that set's
poll calls `ep_item_poll` at the same fuel `n`. -/

theorem epItemPoll_zero (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameWGKernel (Leanux.epItemPoll 0 epiId pt depth) := by
  frame_wg [epItemPoll] using [getEpi_spec, fileIncNotZero_spec, getFile_spec, vfsPoll_spec, fput_spec]

theorem epItemPoll_succ (n : Nat)
    (hinner : ∀ (P : WGKernelView → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epEventpollPollInner n fid wait depth ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄)
    (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameWGKernel (Leanux.epItemPoll (n + 1) epiId pt depth) := by
  frame_wg [epItemPoll] using [getEpi_spec, fileIncNotZero_spec, getFile_spec, vfsPoll_spec, fput_spec, hinner]

theorem epEventpollPollInner_of_item (fuel : Nat)
    (hitem : ∀ (P : WGKernelView → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄)
    (fid : FileId) (wait : PollTable) (depth : Nat) :
    SameWGKernel (Leanux.epEventpollPollInner fuel fid wait depth) := by
  frame_wg [epEventpollPollInner] using [getFile_spec, epOf_spec, pollWait_spec, epStartScan_spec,
    getEpi_spec, setEpi_spec, epDoneScan_spec, hitem]

theorem epPollAt_specs (fuel : Nat) :
    (∀ (P : WGKernelView → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) ∧
    (∀ (P : WGKernelView → Prop) (fid : FileId) (wait : PollTable) (depth : Nat),
      ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epEventpollPollInner fuel fid wait depth ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄) := by
  induction fuel with
  | zero =>
    have item := fun P epiId pt depth => (epItemPoll_zero epiId pt depth).wp P
    exact ⟨item, fun P fid wait depth => (epEventpollPollInner_of_item 0 item fid wait depth).wp P⟩
  | succ n ih =>
    have item := fun P epiId pt depth => (epItemPoll_succ n ih.2 epiId pt depth).wp P
    exact ⟨item, fun P fid wait depth => (epEventpollPollInner_of_item (n + 1) item fid wait depth).wp P⟩

theorem epItemPoll_spec (P : WGKernelView → Prop) (fuel : Nat) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epItemPoll fuel epiId pt depth
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epPollAt_specs fuel).1 P epiId pt depth

theorem epItemPollAt_sameWGKernel (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    SameWGKernel (Leanux.epItemPollAt epiId pt depth) := by
  frame_wg [epItemPollAt] using [epItemPoll_spec]

theorem epItemPollAt_spec (P : WGKernelView → Prop) (epiId : EpiId) (pt : PollTable) (depth : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epItemPollAt epiId pt depth
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epItemPollAt_sameWGKernel epiId pt depth).wp P

/-! ## Insertion, modification, delivery -/

theorem epInsert_sameWGKernel (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    SameWGKernel (Leanux.epInsert ep event tfile fd fullCheck) := by
  frame_wg [epInsert] using [getFile_spec, epOf_spec, epAllocEpitem_spec, epRegisterEpitem_spec,
    reversePathCheck_spec, epRemove_spec, getEpi_spec, setEpi_spec, epItemPollAt_spec,
    epSetBusyPollNapiId_spec, getEp_spec, setEp_spec, waitqueueActive_spec, epPollSafewake_spec]

theorem epInsert_spec (P : WGKernelView → Prop) (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epInsert ep event tfile fd fullCheck
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epInsert_sameWGKernel ep event tfile fd fullCheck).wp P

theorem epModify_sameWGKernel (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    SameWGKernel (Leanux.epModify ep epiId event) := by
  frame_wg [epModify] using [getEpi_spec, setEpi_spec, epItemPollAt_spec, getEp_spec, setEp_spec,
    waitqueueActive_spec, epPollSafewake_spec]

theorem epModify_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epModify ep epiId event
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epModify_sameWGKernel ep epiId event).wp P

theorem epollPutUevent_sameWGKernel (revents : UInt32) (data : UInt64) :
    SameWGKernel (Leanux.epollPutUevent revents data) := by
  frame_wg [epollPutUevent] using []

theorem epollPutUevent_spec (P : WGKernelView → Prop) (revents : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epollPutUevent revents data
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epollPutUevent_sameWGKernel revents data).wp P

theorem epDeliverEvent_sameWGKernel (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    SameWGKernel (Leanux.epDeliverEvent ep epiId pt) := by
  frame_wg [epDeliverEvent] using [getEpi_spec, setEpi_spec, epItemPollAt_spec, epollPutUevent_spec,
    getEp_spec, setEp_spec]

theorem epDeliverEvent_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epDeliverEvent ep epiId pt
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epDeliverEvent_sameWGKernel ep epiId pt).wp P

theorem epSendEvents_sameWGKernel (ep : EpId) (maxevents : Int) : SameWGKernel (Leanux.epSendEvents ep maxevents) := by
  frame_wg [epSendEvents] using [epStartScan_spec, epDeliverEvent_spec, epDoneScan_spec]

theorem epSendEvents_spec (P : WGKernelView → Prop) (ep : EpId) (maxevents : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epSendEvents ep maxevents
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epSendEvents_sameWGKernel ep maxevents).wp P

/-! ## Waiting -/

theorem epTimeoutToTimespec_sameWGKernel (ms : Int) : SameWGKernel (Leanux.epTimeoutToTimespec ms) := by
  frame_wg [epTimeoutToTimespec] using []

theorem epTimeoutToTimespec_spec (P : WGKernelView → Prop) (ms : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epTimeoutToTimespec ms
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epTimeoutToTimespec_sameWGKernel ms).wp P

theorem epEventsAvailable_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epEventsAvailable ep) := by
  frame_wg [epEventsAvailable] using [getEp_spec]

theorem epEventsAvailable_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epEventsAvailable ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epEventsAvailable_sameWGKernel ep).wp P

theorem epPoll_sameWGKernel (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    SameWGKernel (Leanux.epPoll ep maxevents timeout) := by
  frame_wg [epPoll] using [epEventsAvailable_spec, epSendEvents_spec]

theorem epPoll_spec (P : WGKernelView → Prop) (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epPoll ep maxevents timeout
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epPoll_sameWGKernel ep maxevents timeout).wp P

theorem doEpollWait_sameWGKernel (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    SameWGKernel (Leanux.doEpollWait epfd maxevents to) := by
  frame_wg [doEpollWait] using [fdget_spec, fdput_spec, getFile_spec, epOf_spec, epPoll_spec]

theorem doEpollWait_spec (P : WGKernelView → Prop) (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doEpollWait epfd maxevents to
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doEpollWait_sameWGKernel epfd maxevents to).wp P

/-! ## Creation -/

theorem doEpollCreate_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.doEpollCreate flags) := by
  frame_wg [doEpollCreate] using [epAlloc_spec, getUnusedFdFlags_spec, epClearAndPut_spec,
    anonInodeGetfile_spec, putUnusedFd_spec, getEp_spec, setEp_spec, fdInstall_spec]

theorem doEpollCreate_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doEpollCreate flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doEpollCreate_sameWGKernel flags).wp P

/-! ## The loop checks, by induction on their fuel -/

theorem epollMutexLock_sameWGKernel (nonblock : Bool) : SameWGKernel (Leanux.epollMutexLock nonblock) := by
  frame_wg [epollMutexLock] using []

theorem epollMutexLock_spec (P : WGKernelView → Prop) (nonblock : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epollMutexLock nonblock
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epollMutexLock_sameWGKernel nonblock).wp P

theorem epLoopCheckProc_spec (fuel : Nat) : ∀ (P : WGKernelView → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epLoopCheckProc fuel ep depth
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P ep depth
    have h : SameWGKernel (Leanux.epLoopCheckProc 0 ep depth) := by
      frame_wg [epLoopCheckProc] using []
    exact h.wp P
  | succ n ih =>
    intro P ep depth
    have h : SameWGKernel (Leanux.epLoopCheckProc (n + 1) ep depth) := by
      frame_wg [epLoopCheckProc] using [getEp_spec, setEp_spec, getEpi_spec, getFile_spec, epOf_spec,
        listFile_spec, ih]
    exact h.wp P

theorem epGetUpwardsDepthProc_spec (fuel : Nat) : ∀ (P : WGKernelView → Prop) (ep : EpId) (depth : Nat),
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epGetUpwardsDepthProc fuel ep depth
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := by
  induction fuel with
  | zero =>
    intro P ep depth
    have h : SameWGKernel (Leanux.epGetUpwardsDepthProc 0 ep depth) := by
      frame_wg [epGetUpwardsDepthProc] using []
    exact h.wp P
  | succ n ih =>
    intro P ep depth
    have h : SameWGKernel (Leanux.epGetUpwardsDepthProc (n + 1) ep depth) := by
      frame_wg [epGetUpwardsDepthProc] using [getEp_spec, setEp_spec, getEpi_spec, ih]
    exact h.wp P

theorem epLoopCheck_sameWGKernel (ep to : EpId) : SameWGKernel (Leanux.epLoopCheck ep to) := by
  have loop_spec := epLoopCheckProc_spec (EP_MAX_NESTS + 2)
  have up_spec := epGetUpwardsDepthProc_spec (EP_MAX_NESTS + 2)
  frame_wg [epLoopCheck] using [loop_spec, up_spec]

theorem epLoopCheck_spec (P : WGKernelView → Prop) (ep to : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epLoopCheck ep to
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epLoopCheck_sameWGKernel ep to).wp P

/-! ## ctl -/

theorem doEpollCtlBody_sameWGKernel (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameWGKernel ((pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data) := by
  frame_wg [_private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody] using [getFile_spec, fopsOf_spec,
    epOf_spec, epollMutexLock_spec, getEp_spec, epLoopCheck_spec, epFind_spec, epInsert_spec, epRemove_spec,
    getEpi_spec, epModify_spec]

theorem doEpollCtlBody_spec (P : WGKernelView → Prop) (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ (pinned_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doEpollCtlBody_sameWGKernel fId tId op fd events data).wp P

theorem doEpollCtl_sameWGKernel (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameWGKernel (Leanux.doEpollCtl epfd op fd events data) := by
  frame_wg [doEpollCtl] using [fdget_spec, fdput_spec, doEpollCtlBody_spec, clearTfileCheckList_spec]

theorem doEpollCtl_spec (P : WGKernelView → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doEpollCtl_sameWGKernel epfd op fd events data).wp P

/-! ## The system calls -/

theorem sysEpollCreate1_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.sysEpollCreate1 flags) := by
  frame_wg [sysEpollCreate1] using [doEpollCreate_spec]

theorem sysEpollCreate1_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysEpollCreate1 flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysEpollCreate1_sameWGKernel flags).wp P

theorem sysEpollCtl_sameWGKernel (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    SameWGKernel (Leanux.sysEpollCtl epfd op fd events data) := by
  frame_wg [sysEpollCtl] using [doEpollCtl_spec]

theorem sysEpollCtl_spec (P : WGKernelView → Prop) (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysEpollCtl epfd op fd events data
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysEpollCtl_sameWGKernel epfd op fd events data).wp P

theorem sysEpollWait_sameWGKernel (epfd : Nat) (maxevents timeout : Int) :
    SameWGKernel (Leanux.sysEpollWait epfd maxevents timeout) := by
  frame_wg [sysEpollWait] using [epTimeoutToTimespec_spec, doEpollWait_spec]

theorem sysEpollWait_spec (P : WGKernelView → Prop) (epfd : Nat) (maxevents timeout : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysEpollWait epfd maxevents timeout
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysEpollWait_sameWGKernel epfd maxevents timeout).wp P

end Leanux.Proofs.Framing.EventpollFrames
