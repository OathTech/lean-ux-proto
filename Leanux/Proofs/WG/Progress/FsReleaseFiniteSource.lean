import Leanux.Proofs.WG.Progress.FsPipeCallerFiniteSource
import Leanux.Syscalls

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-- A single callback seam in the actual final-put body. Every guard, access
payment, dentry effect and namespace cleanup queue event remains literal. -/
def fputFinalWith (release : FileId → Option FopsId → FS.M Int) (fid : FileId) : FS.M Unit := do
  let f ← getFile fid
  if ← branchCmp .fputFinalNotOpened (!hasFlag f.fMode FMODE_OPENED) (f.fMode &&& FMODE_OPENED).toNat 0 then
    fileFree fid
    return
  -- might_sleep(); fsnotify_close (compiled out)
  -- eventpoll_release (include/linux/eventpoll.h:34-54): `!READ_ONCE(file->f_ep)`
  if ← branch .eventpollReleaseLinked (f.fEp != .null) then
    eventpollReleaseFile fid
  -- locks_remove_file: a cut point (no locks); security_file_release (compiled out)
  let fop ← fopsOf f.fOp
  if ← branchCmp .fputFinalFasync (hasFlag f.fFlags FASYNC) (f.fFlags &&& FASYNC).toNat 0 then
    unsupported "__fput with FASYNC"
  if ← branch .fputFinalRelease fop.release then
    _ ← release fid f.fOp
  -- `S_ISCHR(inode->i_mode) && inode->i_cdev != NULL && !(mode & FMODE_PATH)`
  if ← branch .fputFinalCharDevice (← inodeIsChr f.fInode) then
    _ ← branch .fputFinalHasCdev true
    _ ← branch .fputFinalNotPath (!hasFlag f.fMode FMODE_PATH)
    unsupported "cdev_put"
  -- fops_put: eventfd_fops has no module owner
  -- file_f_owner_release (fcntl.c:116-125)
  if ← branch .fileOwnerRelease f.fOwner then
    unsupported "file_f_owner_release with an owner"
  putFileAccess f
  -- dput(dentry): a pipe file's pseudo dentry counts its references
  -- (`dputPipefs`); every other file's pseudo dentry is a cut point whose
  -- last reference puts its inode (`dentry_unlink_inode` -> `iput`, reported
  -- by `iputReport`): the shared anonymous inode of eventfd and epoll keeps
  -- its pinned reference, a socket's or a namespace pin's inode is freed
  match f.fInode with
  | some (.pipefs id) => dputPipefs id
  | some (.fixture _) => iputReport true
  | some .anon | none => iputReport false
  -- W8: the pin's nsfs dentry goes with the file's last reference
  -- (`nsfs_evict` -> `ns->ops->put` -> `put_net`): the creating namespace's
  -- last reference, by the fixture's order (the sockets' RCU-deferred puts
  -- ran first), so `cleanup_net` is queued here, with its queue record
  if let some (.fixture "netns-pin") := f.fInode then queueDeviceWork .netnsCleanup
  if ← branchCmp .fputFinalNeedUnmount (hasFlag f.fMode FMODE_NEED_UNMOUNT) (f.fMode &&& FMODE_NEED_UNMOUNT).toNat 0 then
    unsupported "dissolve_on_fput"
  -- mntput(mnt)
  fileFree fid

theorem fputFinalWith_source (fid : FileId) :
    Leanux.fputFinal fid = fputFinalWith Leanux.fopRelease fid := rfl

def fputFinal (fid : FileId) : FS.M Unit := fputFinalWith fopRelease fid

theorem fputFinal_source (fid : FileId) : Leanux.fputFinal fid = fputFinal fid := by
  rw [fputFinalWith_source]
  have same : Leanux.fopRelease = fopRelease := funext fun file => funext (fopRelease_source file)
  rw [same]
  rfl

def fputSync (fid : FileId) : FS.M Unit := do
  let f ← getFile fid
  setFile fid { f with fCount := f.fCount - 1 }
  if ← branch .fputSyncLast (f.fCount == 1) then
    fputFinal fid

theorem fputSync_source (fid : FileId) : Leanux.fputSync fid = fputSync fid := by
  unfold Leanux.fputSync fputSync
  rw [fputFinal_source]

/-- The original bounded task-work loop, including newly enqueued final puts
and the original exhausted-fuel invariant. No drain adequacy is claimed. -/
def taskWorkRun : FS.M Unit := do
  for _ in [0:TASK_WORK_FUEL] do
    match (← getTask .task).taskWorks with
    | [] => return
    | fid :: rest =>
      modifyTask .task fun t => { t with taskWorks := rest }
      fputFinal fid
  invariant "task_work_run did not drain the task's work"

theorem taskWorkRun_source : Leanux.taskWorkRun = taskWorkRun := by
  unfold Leanux.taskWorkRun taskWorkRun
  have same : Leanux.fputFinal = fputFinal := funext fputFinal_source
  rw [same]
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
