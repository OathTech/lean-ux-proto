import Leanux.FS.File

/-!
# fs/pipe.c — `pipe2`

`get_pipe_inode`, `create_pipe_files` (with `alloc_file_clone`,
fs/file_table.c, and `stream_open`, fs/open.c), `__do_pipe_flags`,
`do_pipe2` and the `pipe2` syscall. The pipe's operations are in
`Leanux.FS.Pipe`; the inode helpers (`new_inode_pseudo`,
`simple_inode_init_ts`, `iput`) in `Leanux.FS.Inode`.
-/

namespace Leanux

/-- `FMODE_PREAD`, `FMODE_PWRITE` (include/linux/fs.h). -/
def FMODE_PREAD : UInt32 := (1 : UInt32) <<< 3
def FMODE_PWRITE : UInt32 := (1 : UInt32) <<< 4

/-- get_pipe_inode (fs/pipe.c:880-918). `inode->i_ino = get_next_ino()` lies
    inside the inode-allocation cut (`newInodePseudo`); `i_fop`, `i_uid` and
    `i_gid` (root) are not read on these paths. -/
def getPipeInode : M (Option PipefsInodeId) := do
  let ino? ← newInodePseudo  -- new_inode_pseudo(pipe_mnt->mnt_sb)
  if ← branch .getPipeInodeNoInode ino?.isNone then return none  -- fail_inode
  let some ino := ino? | invariant "unreachable"
  let pipe? ← allocPipeInfo
  if ← branch .getPipeInodeNoPipe pipe?.isNone then
    iputPipefs ino  -- fail_iput
    return none
  let some pid := pipe? | invariant "unreachable"
  setInode ino { (← getInode ino) with iPipe := some pid }
  setPipe pid { (← getPipe pid) with files := 2, readers := 1, writers := 1 }
  -- inode->i_fop = &pipefifo_fops
  setInode ino { (← getInode ino) with iState := I_DIRTY, iMode := S_IFIFO ||| S_IRUSR ||| S_IWUSR }
  -- inode->i_uid = current_fsuid(); inode->i_gid = current_fsgid()
  _ ← simpleInodeInitTs ino
  return some ino

/-- alloc_file_clone (fs/file_table.c:427-438): `alloc_file(&base->f_path,
    ...)` and, on success, `path_get(&f->f_path)`: `mntget` is a cut, `dget`
    takes a reference to the pipefs dentry (`Inode.dCount`).
    `f->f_mapping = base->f_mapping` is not mirrored. -/
def allocFileClone (base : FileId) (flags : UInt32) (fopId : FopsId) : M (Except Int FileId) := do
  let some inode := (← getFile base).fInode | invariant "alloc_file_clone of a file with a NULL f_inode"
  let f ← allocFile flags fopId inode
  if ← branch .allocFileCloneOk (f matches .ok _) then
    match inode with
    | .pipefs ino => setInode ino { (← getInode ino) with dCount := (← getInode ino).dCount + 1 }
    | _ => unsupported "alloc_file_clone of a file outside pipefs"
  return f

/-- stream_open (fs/open.c:1654-1659). -/
def streamOpen (fid : FileId) : M Unit := do
  let f ← getFile fid
  setFile fid { f with fMode := (f.fMode &&& ~~~(FMODE_LSEEK ||| FMODE_PREAD ||| FMODE_PWRITE ||| FMODE_ATOMIC_POS))
                                  ||| FMODE_STREAM }

/-- create_pipe_files (fs/pipe.c:920-963): `res[0]`, the read end, and
    `res[1]`, the write end. -/
def createPipeFiles (flags : UInt32) : M (Except Int (FileId × FileId)) := do
  let ino? ← getPipeInode
  if ← branch .createPipeFilesNoInode ino?.isNone then return .error (-ENFILE)
  let some ino := ino? | invariant "unreachable"
  let iPipe : M PipeId := do
    match (← getInode ino).iPipe with
    | some pid => pure pid
    | none => invariant "create_pipe_files: inode->i_pipe is NULL"
  if ← branchCmp .createPipeFilesNotification (hasFlag flags O_NOTIFICATION_PIPE)
      (flags &&& O_NOTIFICATION_PIPE).toNat 0 then
    -- error = watch_queue_init(inode->i_pipe): the -ENOPKG stub
    -- (include/linux/watch_queue.h:126-128); `if (error)` folds away
    freePipeInfo (← iPipe)
    iputPipefs ino
    return .error (-ENOPKG)
  let f ← allocFilePseudo (O_WRONLY ||| (flags &&& (O_NONBLOCK ||| O_DIRECT))) (.pipefs ino) .pipefifo
  if ← branch .createPipeFilesWriterErr (f matches .error _) then
    freePipeInfo (← iPipe)
    iputPipefs ino
    return match f with | .error e => .error e | .ok _ => .error 0
  let .ok fw := f | invariant "unreachable"
  let pid ← iPipe
  setFile fw { (← getFile fw) with privateData := some (.pipe pid), fPipe := 0 }
  let r ← allocFileClone fw (O_RDONLY ||| (flags &&& O_NONBLOCK)) .pipefifo
  if ← branch .createPipeFilesReaderErr (r matches .error _) then
    putPipeInfo ino pid
    fput fw
    return match r with | .error e => .error e | .ok _ => .error 0
  let .ok fr := r | invariant "unreachable"
  setFile fr { (← getFile fr) with privateData := some (.pipe pid), fPipe := 0 }
  streamOpen fr
  streamOpen fw
  return .ok (fr, fw)

/-- The flags `__do_pipe_flags` accepts (fs/pipe.c:970). -/
def PIPE2_FLAGS : UInt32 := O_CLOEXEC ||| O_NONBLOCK ||| O_DIRECT ||| O_NOTIFICATION_PIPE

/-- __do_pipe_flags (fs/pipe.c:965-1001): the descriptors `fd[0]`, `fd[1]` and
    the files `files[0]`, `files[1]`. `audit_fd_pair` is compiled out
    (`CONFIG_AUDIT` unset). -/
def doPipeFlags (flags : UInt32) : M (Except Int (Nat × Nat × FileId × FileId)) := do
  if ← branchCmp .doPipeFlagsInvalid (flags &&& ~~~PIPE2_FLAGS != 0) (flags &&& ~~~PIPE2_FLAGS).toNat 0 then
    return .error (-EINVAL)
  let files ← createPipeFiles flags
  let error : Int := match files with | .error e => e | .ok _ => 0
  if ← branchCmp .doPipeFlagsCreateErr (error != 0) error 0 then return .error error
  let .ok (f0, f1) := files | invariant "unreachable"
  let fdr ← getUnusedFdFlags flags
  if ← branchCmp .doPipeFlagsFdrErr (fdr < 0) fdr 0 then
    -- err_read_pipe:
    fput f0
    fput f1
    return .error fdr
  let fdw ← getUnusedFdFlags flags
  if ← branchCmp .doPipeFlagsFdwErr (fdw < 0) fdw 0 then
    -- err_fdr:
    putUnusedFd fdr.toNat
    fput f0
    fput f1
    return .error fdw
  -- pipe groks IOCB_NOWAIT
  setFile f0 { (← getFile f0) with fMode := (← getFile f0).fMode ||| FMODE_NOWAIT }
  setFile f1 { (← getFile f1) with fMode := (← getFile f1).fMode ||| FMODE_NOWAIT }
  return .ok (fdr.toNat, fdw.toNat, f0, f1)

/-- do_pipe2 (fs/pipe.c:1018-1038) with a valid `fildes`; `copy_to_user` is an
    environment choice point, and the pair it copies is `World.userFds`. -/
def doPipe2 (flags : UInt32) : M Int := do
  let r ← doPipeFlags flags
  let error : Int := match r with | .error e => e | .ok _ => 0
  if ← branchCmp .doPipe2Ok (error == 0) error 0 then
    let .ok (fdr, fdw, f0, f1) := r | invariant "unreachable"
    if ← branch .doPipe2CopyFault !(← envOk .copyToUser) then
      fput f0
      fput f1
      putUnusedFd fdr
      putUnusedFd fdw
      return -EFAULT
    modify fun w => { w with userFds := some (fdr, fdw) }
    fdInstall fdr f0
    fdInstall fdw f1
  return error

/-- SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags) (fs/pipe.c:1040-1043). -/
def sysPipe2 (flags : UInt32) : M Int := doPipe2 flags

end Leanux
