import Leanux.Proofs.Framing.Eventpoll
import Leanux.Proofs.WG.Keypairs.Frames.FSBase
import Leanux.Proofs.WG.Keypairs.Frames.Wait
import Leanux.FS.Eventpoll

/-! Compatibility receive-state framing for the epoll mirror's release path
(`Leanux/FS/Eventpoll.lean`, the epoll carry-over of 2026-10-13): what
`__fput` reaches through `eventpoll_release` and an epoll file's own
`release`. The item, set and wait-queue stores are not the keypair store.
The epoll system calls themselves (create, ctl, wait) are not framed here. -/
namespace Leanux.Proofs.WG.Keypairs.EventpollFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux.Proofs.WG.Keypairs.FSFrames Leanux.Proofs.WG.Keypairs.WaitFrames

theorem epOf_sameSnapshot (f : File) : SameSnapshot (Leanux.epOf f) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epOf_sameWGKernel

theorem epOf_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epOf f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epOf_sameSnapshot f).wp P

theorem fEpItems_sameSnapshot (f : File) : SameSnapshot (Leanux.fEpItems f) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.fEpItems_sameWGKernel

theorem fEpItems_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fEpItems f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fEpItems_sameSnapshot f).wp P

theorem fEpUnlink_sameSnapshot (fid : FileId) (epi : EpiId) : SameSnapshot (Leanux.fEpUnlink fid epi) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.fEpUnlink_sameWGKernel

theorem fEpUnlink_spec (P : Snapshot → Prop) (fid : FileId) (epi : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fEpUnlink fid epi
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fEpUnlink_sameSnapshot fid epi).wp P

theorem fileIncNotZero_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fileIncNotZero fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.fileIncNotZero_sameWGKernel

theorem fileIncNotZero_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileIncNotZero fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileIncNotZero_sameSnapshot fid).wp P

theorem freeEphead_sameSnapshot (head : Bool) : SameSnapshot (Leanux.freeEphead head) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.freeEphead_sameWGKernel

theorem freeEphead_spec (P : Snapshot → Prop) (head : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeEphead head
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeEphead_sameSnapshot head).wp P

theorem epRefcountDecAndTest_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epRefcountDecAndTest ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRefcountDecAndTest_sameWGKernel

theorem epRefcountDecAndTest_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRefcountDecAndTest ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRefcountDecAndTest_sameSnapshot ep).wp P

theorem epFree_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epFree ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epFree_sameWGKernel

theorem epFree_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epFree ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epFree_sameSnapshot ep).wp P

theorem epRemoveWaitQueue_sameSnapshot (pwqId : PwqId) : SameSnapshot (Leanux.epRemoveWaitQueue pwqId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRemoveWaitQueue_sameWGKernel

theorem epRemoveWaitQueue_spec (P : Snapshot → Prop) (pwqId : PwqId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveWaitQueue pwqId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveWaitQueue_sameSnapshot pwqId).wp P

theorem epUnregisterPollwait_sameSnapshot (ep : EpId) (epiId : EpiId) :
    SameSnapshot (Leanux.epUnregisterPollwait ep epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epUnregisterPollwait_sameWGKernel

theorem epUnregisterPollwait_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epUnregisterPollwait ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epUnregisterPollwait_sameSnapshot ep epiId).wp P

theorem epRemoveFile_sameSnapshot (ep : EpId) (epiId : EpiId) (fid : FileId) :
    SameSnapshot (Leanux.epRemoveFile ep epiId fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRemoveFile_sameWGKernel

theorem epRemoveFile_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveFile ep epiId fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveFile_sameSnapshot ep epiId fid).wp P

theorem epRemoveEpi_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRemoveEpi ep epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRemoveEpi_sameWGKernel

theorem epRemoveEpi_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemoveEpi ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemoveEpi_sameSnapshot ep epiId).wp P

theorem epRemove_sameSnapshot (ep : EpId) (epiId : EpiId) : SameSnapshot (Leanux.epRemove ep epiId) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epRemove_sameWGKernel

theorem epRemove_spec (P : Snapshot → Prop) (ep : EpId) (epiId : EpiId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epRemove ep epiId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epRemove_sameSnapshot ep epiId).wp P

theorem epClearAndPut_sameSnapshot (ep : EpId) : SameSnapshot (Leanux.epClearAndPut ep) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epClearAndPut_sameWGKernel

theorem epClearAndPut_spec (P : Snapshot → Prop) (ep : EpId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epClearAndPut ep
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epClearAndPut_sameSnapshot ep).wp P

theorem epEventpollRelease_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.epEventpollRelease fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.epEventpollRelease_sameWGKernel

theorem epEventpollRelease_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.epEventpollRelease fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (epEventpollRelease_sameSnapshot fid).wp P

theorem eventpollReleaseFile_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.eventpollReleaseFile fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.EventpollFrames.eventpollReleaseFile_sameWGKernel

theorem eventpollReleaseFile_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventpollReleaseFile fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventpollReleaseFile_sameSnapshot fid).wp P

end Leanux.Proofs.WG.Keypairs.EventpollFrames
