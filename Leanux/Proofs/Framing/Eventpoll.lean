import Leanux.Proofs.Framing.FSBase
import Leanux.Proofs.Framing.Wait
import Leanux.FS.Eventpoll

/-! Full WireGuard kernel framing for the epoll mirror's release path
(`Leanux/FS/Eventpoll.lean`, the epoll carry-over of 2026-10-13): what
`__fput` reaches through `eventpoll_release` and an epoll file's own
`release`. The item, set and wait-queue stores are outside the full WireGuard kernel view.
The epoll system calls themselves (create, ctl, wait) are not framed here. -/
namespace Leanux.Proofs.Framing.EventpollFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames
open Leanux.Proofs.Framing.FSFrames Leanux.Proofs.Framing.WaitFrames

theorem epOf_sameWGKernel (f : File) : SameWGKernel (Leanux.epOf f) := by
  frame_wg [epOf] using []

theorem epOf_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epOf f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epOf_sameWGKernel f).wp P

theorem fEpItems_sameWGKernel (f : File) : SameWGKernel (Leanux.fEpItems f) := by
  frame_wg [fEpItems] using [getEp_spec]

theorem fEpItems_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fEpItems f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fEpItems_sameWGKernel f).wp P

theorem fEpUnlink_sameWGKernel (fid : FileId) (epi : EpiId) : SameWGKernel (Leanux.fEpUnlink fid epi) := by
  frame_wg [fEpUnlink] using [getFile_spec, setFile_spec, getEp_spec, setEp_spec]

theorem fEpUnlink_spec (P : WGKernelView → Prop) (fid : FileId) (epi : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fEpUnlink fid epi
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fEpUnlink_sameWGKernel fid epi).wp P

theorem fileIncNotZero_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.fileIncNotZero fid) := by
  frame_wg [fileIncNotZero] using [getFile_spec, setFile_spec]

theorem fileIncNotZero_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileIncNotZero fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileIncNotZero_sameWGKernel fid).wp P

theorem freeEphead_sameWGKernel (head : Bool) : SameWGKernel (Leanux.freeEphead head) := by
  frame_wg [freeEphead] using []

theorem freeEphead_spec (P : WGKernelView → Prop) (head : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freeEphead head
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freeEphead_sameWGKernel head).wp P

theorem epRefcountDecAndTest_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epRefcountDecAndTest ep) := by
  frame_wg [epRefcountDecAndTest] using [getEp_spec, setEp_spec, refcountDecAndTest_spec]

theorem epRefcountDecAndTest_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRefcountDecAndTest ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRefcountDecAndTest_sameWGKernel ep).wp P

theorem epFree_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epFree ep) := by
  frame_wg [epFree] using [freeEp_spec]

theorem epFree_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epFree ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epFree_sameWGKernel ep).wp P

theorem epRemoveWaitQueue_sameWGKernel (pwqId : PwqId) : SameWGKernel (Leanux.epRemoveWaitQueue pwqId) := by
  frame_wg [epRemoveWaitQueue] using [getPwq_spec, removeWaitQueue_spec]

theorem epRemoveWaitQueue_spec (P : WGKernelView → Prop) (pwqId : PwqId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRemoveWaitQueue pwqId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRemoveWaitQueue_sameWGKernel pwqId).wp P

theorem epUnregisterPollwait_sameWGKernel (ep : EpId) (epiId : EpiId) :
    SameWGKernel (Leanux.epUnregisterPollwait ep epiId) := by
  frame_wg [epUnregisterPollwait] using [getEpi_spec, setEpi_spec, epRemoveWaitQueue_spec, freePwq_spec]

theorem epUnregisterPollwait_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epUnregisterPollwait ep epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epUnregisterPollwait_sameWGKernel ep epiId).wp P

theorem epRemoveFile_sameWGKernel (ep : EpId) (epiId : EpiId) (fid : FileId) :
    SameWGKernel (Leanux.epRemoveFile ep epiId fid) := by
  frame_wg [epRemoveFile] using [getFile_spec, setFile_spec, fEpItems_spec, getEp_spec, setEp_spec,
    fEpUnlink_spec, freeEphead_spec]

theorem epRemoveFile_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRemoveFile ep epiId fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRemoveFile_sameWGKernel ep epiId fid).wp P

theorem epRemoveEpi_sameWGKernel (ep : EpId) (epiId : EpiId) : SameWGKernel (Leanux.epRemoveEpi ep epiId) := by
  frame_wg [epRemoveEpi] using [getEp_spec, setEp_spec, getEpi_spec, freeEpi_spec]

theorem epRemoveEpi_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRemoveEpi ep epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRemoveEpi_sameWGKernel ep epiId).wp P

theorem epRemove_sameWGKernel (ep : EpId) (epiId : EpiId) : SameWGKernel (Leanux.epRemove ep epiId) := by
  frame_wg [epRemove] using [epUnregisterPollwait_spec, getEpi_spec, fileIncNotZero_spec,
    epRemoveFile_spec, epRemoveEpi_spec, epRefcountDecAndTest_spec, fput_spec]

theorem epRemove_spec (P : WGKernelView → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epRemove ep epiId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epRemove_sameWGKernel ep epiId).wp P

theorem epClearAndPut_sameWGKernel (ep : EpId) : SameWGKernel (Leanux.epClearAndPut ep) := by
  frame_wg [epClearAndPut] using [waitqueueActive_spec, getEp_spec, epUnregisterPollwait_spec,
    epRemove_spec, epRefcountDecAndTest_spec, epFree_spec]

theorem epClearAndPut_spec (P : WGKernelView → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epClearAndPut ep
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epClearAndPut_sameWGKernel ep).wp P

theorem epEventpollRelease_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.epEventpollRelease fid) := by
  frame_wg [epEventpollRelease] using [getFile_spec, epOf_spec, epClearAndPut_spec]

theorem epEventpollRelease_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.epEventpollRelease fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (epEventpollRelease_sameWGKernel fid).wp P

theorem eventpollReleaseFile_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.eventpollReleaseFile fid) := by
  frame_wg [eventpollReleaseFile] using [getFile_spec, fEpItems_spec, getEpi_spec, setEpi_spec,
    epUnregisterPollwait_spec, epRemoveFile_spec, epRemoveEpi_spec, epRefcountDecAndTest_spec]

theorem eventpollReleaseFile_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventpollReleaseFile fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventpollReleaseFile_sameWGKernel fid).wp P

end Leanux.Proofs.Framing.EventpollFrames
