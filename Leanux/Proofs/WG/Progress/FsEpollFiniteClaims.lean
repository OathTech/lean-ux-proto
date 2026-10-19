import Leanux.Proofs.WG.Progress.FsEpollControlFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Unrestricted projected agreements. The source equations preserve
full native FS/task/Ambient results and Stops, including native fuel errors. -/

theorem original_epPtableQueueProc_finite (fid : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epPtableQueueProc fid whead pt)) (liftFS (epPtableQueueProc fid whead pt)) := by
  rw [epPtableQueueProc_source]
  intro w pre
  rfl

theorem original_pollWait_finite (fid : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.pollWait fid whead pt)) (liftFS (pollWait fid whead pt)) := by
  rw [pollWait_source]
  intro w pre
  rfl

theorem original_pipePoll_finite (fid : FileId) (wait : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.pipePoll fid wait)) (liftFS (pipePoll fid wait)) := by
  rw [pipePoll_source]
  intro w pre
  rfl

theorem original_eventfdPoll_finite (fid : FileId) (wait : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.eventfdPoll fid wait)) (liftFS (eventfdPoll fid wait)) := by
  rw [eventfdPoll_source]
  intro w pre
  rfl

theorem original_fopPoll_finite (fid : FileId) (pt : PollTable) (ops : Option FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fopPoll fid pt ops)) (liftFS (fopPoll fid pt ops)) := by
  rw [fopPoll_source]
  intro w pre
  rfl

theorem original_vfsPoll_finite (fid : FileId) (pt : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.vfsPoll fid pt)) (liftFS (vfsPoll fid pt)) := by
  rw [vfsPoll_source]
  intro w pre
  rfl

theorem original_epAlloc_finite :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epAlloc)) (liftFS (epAlloc)) := by
  rw [epAlloc_source]
  intro w pre
  rfl

theorem original_epAttachFile_finite (fid : FileId) (epiId : EpiId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epAttachFile fid epiId)) (liftFS (epAttachFile fid epiId)) := by
  rw [epAttachFile_source]
  intro w pre
  rfl

theorem original_epAllocEpitem_finite (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epAllocEpitem ep event tfile fd)) (liftFS (epAllocEpitem ep event tfile fd)) := by
  rw [epAllocEpitem_source]
  intro w pre
  rfl

theorem original_epRegisterEpitem_finite (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epRegisterEpitem ep epiId tep fullCheck)) (liftFS (epRegisterEpitem ep epiId tep fullCheck)) := by
  rw [epRegisterEpitem_source]
  intro w pre
  rfl

theorem original_doEpollCreate_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doEpollCreate flags)) (liftFS (doEpollCreate flags)) := by
  rw [doEpollCreate_source]
  intro w pre
  rfl

theorem original_sysEpollCreate1_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysEpollCreate1 flags)) (liftFS (sysEpollCreate1 flags)) := by
  rw [sysEpollCreate1_source]
  intro w pre
  rfl

theorem original_epItemPoll_finite (fuel : Nat) (epi : EpiId) (pt : PollTable) (depth : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epItemPoll fuel epi pt depth)) (liftFS (epItemPoll fuel epi pt depth)) := by
  rw [epItemPoll_source]
  intro w pre
  rfl

theorem original_epEventpollPollInner_finite (fuel : Nat) (fid : FileId) (pt : PollTable) (depth : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epEventpollPollInner fuel fid pt depth)) (liftFS (epEventpollPollInner fuel fid pt depth)) := by
  rw [epEventpollPollInner_source]
  intro w pre
  rfl

theorem original_epItemPollAt_finite (epi : EpiId) (pt : PollTable) (depth : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epItemPollAt epi pt depth)) (liftFS (epItemPollAt epi pt depth)) := by
  rw [epItemPollAt_source]
  intro w pre
  rfl

theorem original_epInsert_finite (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epInsert ep event tfile fd fullCheck)) (liftFS (epInsert ep event tfile fd fullCheck)) := by
  rw [epInsert_source]
  intro w pre
  rfl

theorem original_epModify_finite (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epModify ep epiId event)) (liftFS (epModify ep epiId event)) := by
  rw [epModify_source]
  intro w pre
  rfl

theorem original_doEpollCtl_finite (epfd : Nat) (op fd : Int) (events : UInt32) (data : UInt64) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doEpollCtl epfd op fd events data)) (liftFS (doEpollCtl epfd op fd events data)) := by
  rw [doEpollCtl_source]
  intro w pre
  rfl

theorem original_sysEpollCtl_finite (epfd : Nat) (op fd : Int) (events : UInt32) (data : UInt64) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysEpollCtl epfd op fd events data)) (liftFS (sysEpollCtl epfd op fd events data)) := by
  rw [sysEpollCtl_source]
  intro w pre
  rfl


end Leanux.Proofs.WG.Progress.FsFinite
