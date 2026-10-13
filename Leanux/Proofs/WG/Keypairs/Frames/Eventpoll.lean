import Leanux.Proofs.WG.Keypairs.Frames.FSBase
import Leanux.Proofs.WG.Keypairs.Frames.Wait
import Leanux.FS.Eventpoll

/-! Receive-state framing for the epoll mirror's release path
(`Leanux/FS/Eventpoll.lean`, the epoll carry-over of 2026-10-13): what
`__fput` reaches through `eventpoll_release` and an epoll file's own
`release`. The item, set and wait-queue stores are not the keypair store.
The epoll system calls themselves (create, ctl, wait) are not framed here. -/
namespace Leanux.Proofs.WG.Keypairs.EventpollFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux.Proofs.WG.Keypairs.FSFrames Leanux.Proofs.WG.Keypairs.WaitFrames

theorem epOf_sameSnapshot (f : File) : SameSnapshot (Leanux.epOf f) := by
  frame_same [epOf] using []

theorem epOf_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epOf f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epOf_sameSnapshot f).wp P

theorem fEpItems_sameSnapshot (f : File) : SameSnapshot (Leanux.fEpItems f) := by
  frame_same [fEpItems] using [getEp_spec]

theorem fEpItems_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fEpItems f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fEpItems_sameSnapshot f).wp P

theorem fEpUnlink_sameSnapshot (fid : FileId) (epi : EpiId) : SameSnapshot (Leanux.fEpUnlink fid epi) := by
  frame_same [fEpUnlink] using [getFile_spec, setFile_spec, getEp_spec, setEp_spec]

theorem fEpUnlink_spec (P : Snapshot → Prop) (fid : FileId) (epi : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fEpUnlink fid epi
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fEpUnlink_sameSnapshot fid epi).wp P

theorem fileIncNotZero_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fileIncNotZero fid) := by
  frame_same [fileIncNotZero] using [getFile_spec, setFile_spec]

theorem fileIncNotZero_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileIncNotZero fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileIncNotZero_sameSnapshot fid).wp P

theorem freeEphead_sameSnapshot (head : Bool) : SameSnapshot (Leanux.freeEphead head) := by
  frame_same [freeEphead] using []

theorem freeEphead_spec (P : Snapshot → Prop) (head : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEphead head
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEphead_sameSnapshot head).wp P

theorem epRefcountDecAndTest_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epRefcountDecAndTest ep) := by
  frame_same [epRefcountDecAndTest] using [getEp_spec, setEp_spec, refcountDecAndTest_spec]

theorem epRefcountDecAndTest_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRefcountDecAndTest ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRefcountDecAndTest_sameSnapshot ep).wp P

theorem epFree_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epFree ep) := by
  frame_same [epFree] using [freeEp_spec]

theorem epFree_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epFree ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epFree_sameSnapshot ep).wp P

theorem epRemoveWaitQueue_sameSnapshot (pwqId : PwqId) : SameSnapshot (Leanux.epRemoveWaitQueue pwqId) := by
  frame_same [epRemoveWaitQueue] using [getPwq_spec, removeWaitQueue_spec]

theorem epRemoveWaitQueue_spec (P : Snapshot → Prop) (pwqId : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveWaitQueue pwqId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveWaitQueue_sameSnapshot pwqId).wp P

theorem epUnregisterPollwait_sameSnapshot (ep : EpId) (epiId : EpiId) :
    SameSnapshot (Leanux.epUnregisterPollwait ep epiId) := by
  frame_same [epUnregisterPollwait] using [getEpi_spec, setEpi_spec, epRemoveWaitQueue_spec, freePwq_spec]

theorem epUnregisterPollwait_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epUnregisterPollwait ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epUnregisterPollwait_sameSnapshot ep epiId).wp P

theorem epRemoveFile_sameSnapshot (ep : EpId) (epiId : EpiId) (fid : FileId) :
    SameSnapshot (Leanux.epRemoveFile ep epiId fid) := by
  frame_same [epRemoveFile] using [getFile_spec, setFile_spec, fEpItems_spec, getEp_spec, setEp_spec,
    fEpUnlink_spec, freeEphead_spec]

theorem epRemoveFile_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveFile ep epiId fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveFile_sameSnapshot ep epiId fid).wp P

theorem epRemoveEpi_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRemoveEpi ep epiId) := by
  frame_same [epRemoveEpi] using [getEp_spec, setEp_spec, getEpi_spec, freeEpi_spec]

theorem epRemoveEpi_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveEpi ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveEpi_sameSnapshot ep epiId).wp P

theorem epRemove_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRemove ep epiId) := by
  frame_same [epRemove] using [epUnregisterPollwait_spec, getEpi_spec, fileIncNotZero_spec,
    epRemoveFile_spec, epRemoveEpi_spec, epRefcountDecAndTest_spec, fput_spec]

theorem epRemove_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemove ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemove_sameSnapshot ep epiId).wp P

theorem epClearAndPut_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epClearAndPut ep) := by
  frame_same [epClearAndPut] using [waitqueueActive_spec, getEp_spec, epUnregisterPollwait_spec,
    epRemove_spec, epRefcountDecAndTest_spec, epFree_spec]

theorem epClearAndPut_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epClearAndPut ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epClearAndPut_sameSnapshot ep).wp P

theorem epEventpollRelease_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.epEventpollRelease fid) := by
  frame_same [epEventpollRelease] using [getFile_spec, epOf_spec, epClearAndPut_spec]

theorem epEventpollRelease_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollRelease fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epEventpollRelease_sameSnapshot fid).wp P

theorem eventpollReleaseFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.eventpollReleaseFile fid) := by
  frame_same [eventpollReleaseFile] using [getFile_spec, fEpItems_spec, getEpi_spec, setEpi_spec,
    epUnregisterPollwait_spec, epRemoveFile_spec, epRemoveEpi_spec, epRefcountDecAndTest_spec]

theorem eventpollReleaseFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventpollReleaseFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventpollReleaseFile_sameSnapshot fid).wp P

end Leanux.Proofs.WG.Keypairs.EventpollFrames
