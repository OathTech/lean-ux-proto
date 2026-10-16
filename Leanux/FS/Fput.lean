import Leanux.FS.Eventpoll

/-!
# fs/file_table.c — `__fput` and `__fput_sync`

The release of a file's last reference, after the epoll mirror it calls:
`eventpoll_release` (include/linux/eventpoll.h:34-54) unlinks a watched
file from its sets before `f_op->release`, and an epoll file's release
tears its set down. The rest of fs/file_table.c is in `Leanux.FS.FileTable`
(stream S moved these two here; docs/2026-10-12-epoll-design.md, 4.6).
-/

namespace Leanux

/-- `f_op->release(inode, file)`. -/
def fopRelease (fid : FileId) : Option FopsId → FS.M Int
  | some .eventfd => eventfdRelease fid
  | some .pipefifo => do
    -- pipe_release(inode, file): `inode` is the file's pipefs inode
    match (← getFile fid).fInode with
    | some (.pipefs ino) => pipeRelease ino fid
    | _ => invariant "a pipefifo file whose f_inode is not a pipefs inode"
  | some .eventpoll => epEventpollRelease fid
  -- W8: sock_close (net/socket.c, unanchored): the socket's release and its
  -- RCU-deferred put_net are a cut point
  | some (.fixture _) => return 0
  | none => invariant "file->f_op is NULL"

/-- __fput (file_table.c:442-482): the release of the last reference. -/
def fputFinal (fid : FileId) : FS.M Unit := do
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
    _ ← fopRelease fid f.fOp
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

/-- __fput_sync (file_table.c:550-554). -/
def fputSync (fid : FileId) : FS.M Unit := do
  let f ← getFile fid
  setFile fid { f with fCount := f.fCount - 1 }
  if ← branch .fputSyncLast (f.fCount == 1) then
    fputFinal fid

end Leanux
