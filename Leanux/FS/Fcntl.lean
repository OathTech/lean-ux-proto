import Leanux.FS.File
import Leanux.FS.FileTable

/-!
# fs/fcntl.c — `fcntl` for F_GETFD, F_SETFD and F_GETFL
-/

namespace Leanux

inductive FcntlCmd where
  | getFD | setFD | getFL | setFL
  /-- `F_SETPIPE_SZ` (1031) and `F_GETPIPE_SZ` (1032),
      include/uapi/linux/fcntl.h:34-35. -/
  | setPipeSz | getPipeSz
  deriving Repr, BEq

/-- `inode->i_flags` and `inode->i_mode & S_IFMT` of the file's inode. The
    anonymous inode (fs/libfs.c, `alloc_anon_inode`) has `i_flags = S_PRIVATE`
    and `i_mode = S_IRUSR | S_IWUSR`, so no file-type bits. A pipefs inode's
    fields are in the inode store (`get_pipe_inode`). -/
def inodeFlags : Option InodeId → M Nat
  | some .anon => return S_PRIVATE
  | some (.pipefs id) => return (← getInode id).iFlags
  | some (.fixture name) => unsupported s!"inode of fixture file {name}"
  | none => invariant "file->f_inode is NULL"

def inodeFileType : Option InodeId → M Nat
  | some .anon => return 0
  | some (.pipefs id) => return (← getInode id).iMode &&& S_IFMT
  | some (.fixture name) => unsupported s!"inode of fixture file {name}"
  | none => invariant "file->f_inode is NULL"

/-- setfl (fcntl.c:39-89). `O_NONBLOCK != O_NDELAY` is false on x86-64, so the
    SunOS test is not a branch in this build. `inode_owner_or_capable` is a cut
    point: the harness runs as root, which is capable. `f_lock` is taken around
    the update. -/
def setfl (fid : FileId) (arg : UInt32) : M Int := do
  let f ← getFile fid
  -- `((arg ^ filp->f_flags) & O_APPEND) && IS_APPEND(inode)`
  if ← branchCmp .setflAppendChanged (hasFlag (arg ^^^ f.fFlags) O_APPEND) ((arg ^^^ f.fFlags) &&& O_APPEND).toNat 0 then
    let iflags ← inodeFlags f.fInode  -- IS_APPEND(inode)
    if ← branchCmp .setflAppendOnly (iflags &&& S_APPEND != 0) (iflags &&& S_APPEND) 0 then return -EPERM
  -- `(arg & O_NOATIME) && !(filp->f_flags & O_NOATIME)`, then the owner check
  if ← branchCmp .setflNoatimeRequested (hasFlag arg O_NOATIME) (arg &&& O_NOATIME).toNat 0 then
    if ← branchCmp .setflNoatimeNotSet (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0 then
      -- inode_owner_or_capable: a cut point; the harness runs as root, so it returns 1
      let ownerOrCapable : Nat := 1
      if ← branchCmp .setflNotOwnerOrCapable (ownerOrCapable == 0) ownerOrCapable 0 then return -EPERM
  -- `!S_ISFIFO(inode->i_mode) && (arg & O_DIRECT) && !(filp->f_mode & FMODE_CAN_ODIRECT)`
  let fileType ← inodeFileType f.fInode
  if ← branchCmp .setflNotFifo (fileType != S_IFIFO) fileType S_IFIFO then
    if ← branchCmp .setflDirect (hasFlag arg O_DIRECT) (arg &&& O_DIRECT).toNat 0 then
      if ← branchCmp .setflCannotOdirect (!hasFlag f.fMode FMODE_CAN_ODIRECT) (f.fMode &&& FMODE_CAN_ODIRECT).toNat 0 then
        return -EINVAL
  let fop ← fopsOf f.fOp
  if ← branch .setflHasCheckFlags fop.checkFlags then unsupported "f_op->check_flags"
  let error : Int := 0
  if ← branch .setflError (error != 0) then return error
  -- `((arg ^ filp->f_flags) & FASYNC) && filp->f_op->fasync`
  if ← branchCmp .setflFasyncChanged (hasFlag (arg ^^^ f.fFlags) FASYNC) ((arg ^^^ f.fFlags) &&& FASYNC).toNat 0 then
    if ← branch .setflHasFasync fop.fasync then unsupported "f_op->fasync"
  -- spin_lock(&filp->f_lock)
  let fFlags := (arg &&& SETFL_MASK) ||| (f.fFlags &&& ~~~SETFL_MASK)
  let fIocbFlags ← iocbFlags fFlags  -- iocb_flags(filp) reads the new f_flags
  setFile fid { f with fFlags, fIocbFlags }
  -- spin_unlock(&filp->f_lock)
  return error

/-- do_fcntl (fcntl.c:443-...): the `switch (cmd)` arm taken is the choice
    point; only the three modeled commands can reach it. -/
def doFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) : M Int := do
  let argi : Int := (arg.toUInt32).toNat  -- (int)arg; only bit 0 is tested
  match cmd with
  | .getFD =>
    _ ← branch .fcntlCaseGetfd true
    let set ← getCloseOnExec fd
    _ ← branch .fcntlGetfdSet set  -- err = get_close_on_exec(fd) ? FD_CLOEXEC : 0
    return if set then FD_CLOEXEC else 0
  | .setFD =>
    _ ← branch .fcntlCaseSetfd true
    setCloseOnExec fd (argi % 2 == 1)  -- argi & FD_CLOEXEC
    return 0
  | .getFL =>
    _ ← branch .fcntlCaseGetfl true
    return (← getFile fid).fFlags.toNat
  | .setFL =>
    _ ← branch .fcntlCaseSetfl true
    setfl fid (argi.toNat.toUInt32)  -- setfl(fd, filp, argi)
  -- `case F_SETPIPE_SZ: case F_GETPIPE_SZ: err = pipe_fcntl(filp, cmd, argi)`
  -- (fcntl.c:538-541); pipe_fcntl takes `unsigned int arg`
  | .setPipeSz | .getPipeSz =>
    _ ← branch .fcntlCasePipeSz true
    pipeFcntl fid (if cmd == .setPipeSz then F_SETPIPE_SZ else F_GETPIPE_SZ) (arg.toUInt32.toNat)

/-- SYSCALL_DEFINE3(fcntl) (fcntl.c:573-594). `security_file_fcntl` is the
    constant 0 (`CONFIG_SECURITY=n`), so `if (!err)` is not a branch here. -/
def sysFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) : M Int := do
  let f ← fdgetRaw fd
  let mut err := -EBADF
  if ← branch .fcntlNoFile f.file.isNone then return err  -- goto out
  let some fid := f.file | invariant "unreachable"
  if ← branchCmp .fcntlPathFile (hasFlag (← getFile fid).fMode FMODE_PATH) ((← getFile fid).fMode &&& FMODE_PATH).toNat 0 then
    unsupported "check_fcntl_cmd for O_PATH files"
  err ← doFcntl fd cmd arg fid
  fdput f  -- out1:
  return err

end Leanux
