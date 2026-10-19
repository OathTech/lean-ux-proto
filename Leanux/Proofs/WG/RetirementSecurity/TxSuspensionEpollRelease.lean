import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionDescriptors

/-! Actual eventpoll release and wait-queue removal affect file-layer state,
with suspended WG worker identities retained by their native ambient leaves. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem wait_queue (r : WaitQueueRef) : Keeps (getWaitQueue r) := by
  nested_suspension_source [getWaitQueue] using [get_pipe,get_ctx,get_ep]

theorem set_wait_queue (r : WaitQueueRef) (q : WaitQueue) : Keeps (setWaitQueue r q) := by
  nested_suspension_source [setWaitQueue] using [get_pipe,get_ctx,get_ep,set_pipe,set_ctx,set_ep]

theorem wait_active (r : WaitQueueRef) : Keeps (waitqueueActive r) := by
  nested_suspension_source [waitqueueActive] using [wait_queue]

theorem wait_remove (r : WaitQueueRef) (e : WaitEntry) : Keeps (removeWaitQueue r e) := by
  nested_suspension_source [removeWaitQueue] using [wait_queue,set_wait_queue,invariant]

theorem ep_of (f : File) : Keeps (epOf f) := by
  nested_suspension_source [epOf] using [invariant]

theorem ep_items (f : File) : Keeps (fEpItems f) := by
  nested_suspension_source [fEpItems] using [get_ep]

theorem ep_unlink (fid : FileId) (epi : EpiId) : Keeps (fEpUnlink fid epi) := by
  nested_suspension_source [fEpUnlink] using [get_file,set_file,get_ep,set_ep]

theorem ephead_free (head : Bool) : Keeps (freeEphead head) := by
  nested_suspension_source [freeEphead] using [branch]

theorem file_inc (fid : FileId) : Keeps (fileIncNotZero fid) := by
  nested_suspension_source [fileIncNotZero] using [get_file,set_file]

theorem refcount_dec (count : Nat) : Keeps ((refcountDecAndTest count : FS.M Bool)) := by
  nested_suspension_source [refcountDecAndTest] using [branch,compare,unsupported]

theorem ep_refcount_dec (ep : EpId) : Keeps (epRefcountDecAndTest ep) := by
  nested_suspension_source [epRefcountDecAndTest] using [get_ep,set_ep,refcount_dec,branch,invariant]

theorem ep_free (ep : EpId) : Keeps (epFree ep) := by
  nested_suspension_source [epFree] using [free_ep]

theorem ep_remove_wait (id : PwqId) : Keeps (epRemoveWaitQueue id) := by
  nested_suspension_source [epRemoveWaitQueue] using [get_pwq,branch,wait_remove]

theorem ep_unregister (ep : EpId) (id : EpiId) : Keeps (epUnregisterPollwait ep id) := by
  nested_suspension_source [epUnregisterPollwait] using [get_epi,set_epi,branch,ep_remove_wait,free_pwq]

theorem ep_remove_file (ep : EpId) (id : EpiId) (fid : FileId) : Keeps (epRemoveFile ep id fid) := by
  nested_suspension_source [epRemoveFile] using [get_file,ep_items,set_file,get_ep,set_ep,branch,ep_unlink,ephead_free]

theorem ep_remove_item (ep : EpId) (id : EpiId) : Keeps (epRemoveEpi ep id) := by
  nested_suspension_source [epRemoveEpi] using [get_ep,set_ep,get_epi,branch,free_epi]

theorem ep_remove (ep : EpId) (id : EpiId) : Keeps (epRemove ep id) := by
  nested_suspension_source [epRemove] using [ep_unregister,get_epi,branch,invariant,file_inc,ep_remove_file,ep_remove_item,ep_refcount_dec,fput_reference]

theorem ep_clear (ep : EpId) : Keeps (epClearAndPut ep) := by
  nested_suspension_source [epClearAndPut] using [branch,wait_active,invariant,get_ep,ep_unregister,ep_remove,ep_refcount_dec,ep_free]

theorem ep_release (fid : FileId) : Keeps (epEventpollRelease fid) := by
  nested_suspension_source [epEventpollRelease] using [get_file,ep_of,branch,ep_clear]

theorem ep_release_file (fid : FileId) : Keeps (eventpollReleaseFile fid) := by
  nested_suspension_source [eventpollReleaseFile] using [get_file,ep_items,branch,get_epi,set_epi,ep_unregister,ep_remove_file,ep_remove_item,ep_refcount_dec,invariant]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
