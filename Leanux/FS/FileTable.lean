import Leanux.FS.EventfdOps
import Leanux.FS.Inode

/-!
# fs/file_table.c — `struct file` allocation and release

`alloc_empty_file`/`init_file`, `file_init_path`, `alloc_file`,
`alloc_file_pseudo`, `fput` and `file_free`; `__fput` and `__fput_sync` are in
`Leanux.FS.Fput`, after the epoll mirror they call into.

Configured-program notes (this `.config`): `CONFIG_SECURITY=n`, so every
`security_*` hook is the constant 0 and its error branch does not exist in the
built code; fsnotify and dnotify are compiled out. `CONFIG_EPOLL=y` and
`CONFIG_FILE_LOCKING=y`: `locks_remove_file` and `locks_remove_posix` are cut
points (contract: the file holds no locks); `eventpoll_release` is mirrored
(`Leanux.FS.Fput`, `Leanux.FS.Eventpoll`).
-/

namespace Leanux

/-- `OPEN_FMODE(flag)` (include/linux/fs.h:3725). -/
def openFmode (flags : UInt32) : UInt32 :=
  ((flags + 1) &&& O_ACCMODE) ||| (flags &&& FMODE_NONOTIFY)

/-- Whether the file's inode is a character device (`S_ISCHR`). The anonymous
    inode has mode S_IRUSR|S_IWUSR (fs/libfs.c); a pipefs inode is `S_IFIFO`;
    fixture inodes are not modeled. -/
def inodeIsChr : Option InodeId → FS.M Bool
  | some .anon => return false
  | some (.pipefs id) => return (← getInode id).iMode &&& S_IFMT == S_IFCHR
  -- W8: the fixture's sockets are S_IFSOCK, the pin's nsfs inode S_IFREG
  | some (.fixture _) => return false
  | none => invariant "file->f_inode is NULL"

/-- file_free (file_table.c:87-98). `put_cred` and the slab free are cut points. -/
def fileFree (fid : FileId) : FS.M Unit := do
  let f ← getFile fid
  if ← branchCmp .fileFreeAccounted (!hasFlag f.fMode FMODE_NOACCOUNT) (f.fMode &&& FMODE_NOACCOUNT).toNat 0 then
    modify fun k => { k with nrFiles := k.nrFiles - 1 }   -- percpu_counter_dec(&nr_files)
  if ← branchCmp .fileFreeBacking (hasFlag f.fMode FMODE_BACKING) (f.fMode &&& FMODE_BACKING).toNat 0 then
    unsupported "backing_file_free"
  -- kmem_cache_free(filp_cachep, f)
  freeFile fid

/-- alloc_empty_file (file_table.c:214-253) with init_file (171-202) inlined:
    `f_flags = flags`, `f_mode = OPEN_FMODE(flags)`, `f_count = 1`. -/
def allocEmptyFile (flags : UInt32) : FS.M (Except Int FileId) := do
  let k ← get
  if ← branch .allocEmptyFileOverMax (k.nrFiles >= k.maxFiles) then
    _ ← branch .allocEmptyFileNotCapable false  -- the harness runs as root: capable(CAP_SYS_ADMIN)
    unsupported "files_stat.max_files reached (percpu recount)"
  if ← branch .allocEmptyFileNoMem (!(← hiddenAlloc .filpAlloc)) then
    return .error (-ENOMEM)
  let fid := k.nextFile
  setFile fid { fFlags := flags, fMode := openFmode flags, fCount := 1 }
  modify fun k => { k with nextFile := fid + 1, nrFiles := k.nrFiles + 1 }
  return .ok fid

/-- `iocb_flags(file)` (include/linux/fs.h:3590-3602), with the IOCB values of
    include/linux/fs.h:351-359 (IOCB_APPEND = RWF_APPEND, ...). -/
def iocbFlags (fFlags : UInt32) : FS.M UInt32 := do
  let mut res : UInt32 := 0
  if ← branchCmp .iocbFlagsAppend (hasFlag fFlags O_APPEND) (fFlags &&& O_APPEND).toNat 0 then res := res ||| 0x10
  if ← branchCmp .iocbFlagsDirect (hasFlag fFlags O_DIRECT) (fFlags &&& O_DIRECT).toNat 0 then res := res ||| ((1 : UInt32) <<< 17)
  if ← branchCmp .iocbFlagsDsync (hasFlag fFlags O_DSYNC) (fFlags &&& O_DSYNC).toNat 0 then res := res ||| 0x2
  if ← branchCmp .iocbFlagsSync (hasFlag fFlags O_SYNC_INTERNAL) (fFlags &&& O_SYNC_INTERNAL).toNat 0 then res := res ||| 0x4
  return res

/-- file_init_path (file_table.c:330-351). The path/mapping fields are cut
    points; `i_readcount_inc` (include/linux/fs.h:3130-3133) counts on the
    inode record (`inodeReadcountInc`). -/
def fileInitPath (fid : FileId) (fopId : FopsId) (inode : InodeId) : FS.M Unit := do
  let fop ← fopsOf (some fopId)
  -- file->f_path = *path; file->f_inode = path->dentry->d_inode; f_mapping; f_wb_err; f_sb_err
  setFile fid { (← getFile fid) with fInode := some inode }
  let f ← getFile fid
  let mut mode := f.fMode
  if ← branch .fileInitPathLlseek fop.llseek then mode := mode ||| FMODE_LSEEK
  if ← branchCmp .fileInitPathModeRead (hasFlag mode FMODE_READ) (mode &&& FMODE_READ).toNat 0 then
    let canRead ← do
      if ← branch .fileInitPathHasRead fop.read then pure true
      else branch .fileInitPathHasReadIter fop.readIter
    if canRead then mode := mode ||| FMODE_CAN_READ
  if ← branchCmp .fileInitPathModeWrite (hasFlag mode FMODE_WRITE) (mode &&& FMODE_WRITE).toNat 0 then
    let canWrite ← do
      if ← branch .fileInitPathHasWrite fop.write then pure true
      else branch .fileInitPathHasWriteIter fop.writeIter
    if canWrite then mode := mode ||| FMODE_CAN_WRITE
  let iocb ← iocbFlags f.fFlags
  mode := mode ||| FMODE_OPENED
  -- file->f_op = fop (file_table.c:348)
  setFile fid { f with fMode := mode, fIocbFlags := iocb, fOp := some fopId }
  if ← branchCmp .fileInitPathReadOnly (mode &&& (FMODE_READ ||| FMODE_WRITE) == FMODE_READ) (mode &&& (FMODE_READ ||| FMODE_WRITE)).toNat FMODE_READ.toNat then
    inodeReadcountInc (some inode)

/-- alloc_file (file_table.c:360-369). -/
def allocFile (flags : UInt32) (fopId : FopsId) (inode : InodeId) : FS.M (Except Int FileId) := do
  let r ← allocEmptyFile flags
  if ← branch .allocFileOk (r matches .ok _) then
    if let .ok fid := r then fileInitPath fid fopId inode
  return r

/-- alloc_path_pseudo (file_table.c:371-380): the dentry (`d_alloc_pseudo`,
    an allocation outcome) holding its first reference; `mntget` and
    `d_instantiate` are cut points. A pipefs inode's pseudo dentry counts
    its references (`Inode.dCount`, dropped by `dputPipefs` in `__fput`);
    the anonymous inode's dentry is a cut point. -/
def allocPathPseudo (inode : InodeId) : FS.M Int := do
  if ← branch .allocPathPseudoFail (!(← hiddenAlloc .dAllocPseudo)) then return -ENOMEM
  if let .pipefs id := inode then
    let ino ← getInode id
    if ino.dCount != 0 then invariant s!"d_alloc_pseudo for pipefs inode {id}, whose dentry exists"
    setInode id { ino with dCount := 1 }
  return 0

/-- alloc_file_pseudo (file_table.c:382-400). On failure, `ihold(inode)` and
    `path_put(&path)`: the dentry's last reference goes, and the `iput` of
    its killing balances the `ihold` (both cuts). -/
def allocFilePseudo (flags : UInt32) (inode : InodeId) (fopId : FopsId) : FS.M (Except Int FileId) := do
  let ret ← allocPathPseudo inode
  if ← branch .allocFilePseudoPathErr (ret != 0) then return .error ret
  let r ← allocFile flags fopId inode
  if ← branch .allocFilePseudoErr (r matches .error _) then
    if let .pipefs id := inode then
      setInode id { (← getInode id) with dCount := 0 }
  return r

/-- put_file_access (fs/internal.h:114-121). -/
def putFileAccess (f : File) : FS.M Unit := do
  if ← branchCmp .putFileAccessReadOnly (f.fMode &&& (FMODE_READ ||| FMODE_WRITE) == FMODE_READ) (f.fMode &&& (FMODE_READ ||| FMODE_WRITE)).toNat FMODE_READ.toNat then
    inodeReadcountDec f.fInode
  else if ← branchCmp .putFileAccessWriter (hasFlag f.fMode FMODE_WRITER) (f.fMode &&& FMODE_WRITER).toNat 0 then
    unsupported "file_put_write_access"

-- `__fput` and `__fput_sync` are in `Leanux.FS.Fput`, after the epoll
-- mirror: `__fput` runs `eventpoll_release_file` and `ep_eventpoll_release`,
-- which run `fput` (below) and the whole epoll slice (stream S).

/-- fput (file_table.c:517-540). The last reference queues `____fput` as task
    work, run on return to user mode (see `Leanux.Syscalls`). -/
def fput (fid : FileId) : FS.M Unit := do
  let f ← getFile fid
  setFile fid { f with fCount := f.fCount - 1 }
  if ← branch .fputLast (f.fCount == 1) then
    if ← branch .fputNotOpened (!hasFlag f.fMode (FMODE_BACKING ||| FMODE_OPENED)) then
      fileFree fid
      return
    let task ← getTask .task
    -- `likely(!in_interrupt() && !(task->flags & PF_KTHREAD))`
    let taskContext ← do
      if ← branch .fputInInterrupt false then pure false  -- system-call context
      else pure !(← branch .fputKthread task.isKthread)
    if taskContext then
      -- init_task_work; `if (!task_work_add(task, &file->f_task_work, TWA_RESUME)) return;`
      if ← branch .fputTaskWorkAddFailed task.exited then
        unsupported "task_work_add after exit_task_work (falls through to delayed fput)"
      -- task_work_add pushes at the head of task->task_works (kernel/task_work.c)
      modifyTask .task fun t => { t with taskWorks := fid :: t.taskWorks }
      return
    unsupported "delayed fput"

end Leanux
