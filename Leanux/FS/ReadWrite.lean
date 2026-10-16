import Leanux.FS.File

/-!
# fs/read_write.c — `read` and `write`

`fsnotify_access`/`fsnotify_modify` are compiled out; `add_rchar`,
`add_wchar`, `inc_syscr` and `inc_syscw` are task accounting cut points.
`access_ok` is an environment choice point (the harness passes valid buffers).
-/

namespace Leanux

/-- rw_verify_area (read_write.c:448-475). `security_file_permission` is the
    constant 0 (`CONFIG_SECURITY=n`); `fsnotify_file_area_perm` returns 0
    without fsnotify. `unsigned_offsets` is only reached for negative
    positions, which never arise from `f_pos = 0`. -/
def rwVerifyArea (ppos : Option Int) (count : Nat) : FS.M Int := do
  if ← branchCmp .rwVerifyNegativeCount (count >= 2 ^ 63) count 0 then return -EINVAL
  if ← branch .rwVerifyHasPos ppos.isSome then
    let pos := ppos.getD 0
    if ← branch .rwVerifyNegativePos (pos < 0) then
      unsupported "rw_verify_area with a negative position"
    else if ← branch .rwVerifyPosOverflow (pos + count >= 2 ^ 63) then
      unsupported "rw_verify_area position overflow"
  return 0

/-- new_sync_read (read_write.c:478-493). `init_sync_kiocb` copies
    `f_iocb_flags`; `iov_iter_ubuf` describes the caller's buffer. -/
def newSyncRead (fid : FileId) (len : Nat) (ppos : Option Int) : FS.M (Int × Option Int) := do
  let f ← getFile fid
  let iocb : Kiocb := { filp := fid, kiFlags := f.fIocbFlags, kiPos := ppos.getD 0 }
  let ret ← fopReadIter iocb len f.fOp
  if ← branch .newSyncReadQueued (ret == -529) then  -- BUG_ON(ret == -EIOCBQUEUED)
    unsupported "new_sync_read: -EIOCBQUEUED"
  -- if (ppos) *ppos = kiocb.ki_pos; eventfd_read leaves ki_pos unchanged
  return (ret, ppos.map fun _ => iocb.kiPos)

/-- vfs_read (read_write.c:549-578). -/
def vfsRead (fid : FileId) (count : Nat) (pos : Option Int) : FS.M (Int × Option Int) := do
  let f ← getFile fid
  if ← branchCmp .vfsReadNotReadable (!hasFlag f.fMode FMODE_READ) (f.fMode &&& FMODE_READ).toNat 0 then return (-EBADF, pos)
  if ← branchCmp .vfsReadCannotRead (!hasFlag f.fMode FMODE_CAN_READ) (f.fMode &&& FMODE_CAN_READ).toNat 0 then return (-EINVAL, pos)
  -- `access_ok(buf, count)`: the guest passes a valid user buffer (a trace
  -- input under A-U, docs/2026-10-05-a-alloc.md 6.5)
  if ← branch .vfsReadAccessFault false then return (-EFAULT, pos)
  let ret ← rwVerifyArea pos count
  if ← branch .vfsReadVerifyError (ret != 0) then return (ret, pos)
  let count := if ← branch .vfsReadClamp (count > MAX_RW_COUNT) then MAX_RW_COUNT else count
  let fop ← fopsOf f.fOp
  let (ret, pos) ← do
    if ← branch .vfsReadHasRead fop.read then unsupported "f_op->read"
    else if ← branch .vfsReadHasReadIter fop.readIter then newSyncRead fid count pos
    else pure (-EINVAL, pos)
  if ← branch .vfsReadPositive (ret > 0) then pure ()  -- fsnotify_access; add_rchar
  -- inc_syscr(current)
  return (ret, pos)

/-- `file_ppos` (read_write.c:695-699). -/
def filePpos (f : File) : FS.M (Option Int) := do
  if ← branchCmp .filePposStream (hasFlag f.fMode FMODE_STREAM) (f.fMode &&& FMODE_STREAM).toNat 0 then return none
  return some f.fPos

/-- ksys_read (read_write.c:701-718) and SYSCALL_DEFINE3(read). -/
def ksysRead (fd : Nat) (count : Nat) : FS.M Int := do
  let f ← fdgetPos fd
  let mut ret := -EBADF
  if ← branch .ksysReadHasFile f.file.isSome then
    let some fid := f.file | invariant "unreachable"
    let ppos ← filePpos (← getFile fid)
    _ ← branch .ksysReadHasPpos ppos.isSome  -- pos = *ppos; ppos = &pos
    let (r, pos) ← vfsRead fid count ppos
    ret := r
    if ← branch .ksysReadRetNonneg (ret >= 0) then
      if ← branch .ksysReadStorePos pos.isSome then
        setFile fid { (← getFile fid) with fPos := pos.getD 0 }
    fdputPos f
  return ret

/-- Whether the file's inode is a regular file (`S_ISREG`). The anonymous
    inode has mode S_IRUSR|S_IWUSR, with no file-type bits; a pipefs inode's
    `i_mode` is `S_IFIFO | S_IRUSR | S_IWUSR` (fs/pipe.c:906). -/
def inodeIsReg : Option InodeId → FS.M Bool
  | some .anon => return false
  | some (.pipefs id) => return (← getInode id).iMode &&& S_IFMT == S_IFREG
  | some (.fixture name) => unsupported s!"inode of fixture file {name}"
  | none => invariant "file->f_inode is NULL"

/-- `file_start_write` (include/linux/fs.h:2996-3001). -/
def fileStartWrite (f : File) : FS.M Unit := do
  if ← branch .fileStartWriteNotRegular !(← inodeIsReg f.fInode) then return
  unsupported "sb_start_write"

/-- `file_end_write` (include/linux/fs.h:3016-3021). -/
def fileEndWrite (f : File) : FS.M Unit := do
  if ← branch .fileEndWriteNotRegular !(← inodeIsReg f.fInode) then return
  unsupported "sb_end_write"

/-- new_sync_write (read_write.c:580-595): the `write_iter` arm of
    `vfs_write` (P design section 4). `init_sync_kiocb` copies
    `f_iocb_flags`; `iov_iter_ubuf` describes the first `len` bytes of the
    caller's buffer. `ppos` is NULL for `FMODE_STREAM` files (pipes). -/
def newSyncWrite (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) : FS.M Int := do
  let f ← getFile fid
  let iocb : Kiocb := { filp := fid, kiFlags := f.fIocbFlags, kiPos := ppos.getD 0 }
  if len > buf.size then invariant "new_sync_write: the caller's buffer is shorter than len"
  let ret ← fopWriteIter iocb { bytes := buf.extract 0 len } f.fOp
  if ← branch .newSyncWriteQueued (ret == -529) then  -- BUG_ON(ret == -EIOCBQUEUED)
    unsupported "new_sync_write: -EIOCBQUEUED"
  -- `if (ret > 0 && ppos) *ppos = kiocb.ki_pos`: pipe_write leaves ki_pos
  if ← branchCmp .newSyncWritePositive (ret > 0) ret 0 then
    _ ← branch .newSyncWritePpos ppos.isSome
  return ret

/-- vfs_write (read_write.c:663-693). `buf` is the caller's buffer. -/
def vfsWrite (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) : FS.M Int := do
  let f ← getFile fid
  if ← branchCmp .vfsWriteNotWritable (!hasFlag f.fMode FMODE_WRITE) (f.fMode &&& FMODE_WRITE).toNat 0 then return -EBADF
  if ← branchCmp .vfsWriteCannotWrite (!hasFlag f.fMode FMODE_CAN_WRITE) (f.fMode &&& FMODE_CAN_WRITE).toNat 0 then return -EINVAL
  -- `access_ok(buf, count)`: a valid user buffer (as in vfsRead)
  if ← branch .vfsWriteAccessFault false then return -EFAULT
  let ret ← rwVerifyArea pos count
  if ← branch .vfsWriteVerifyError (ret != 0) then return ret
  let count := if ← branch .vfsWriteClamp (count > MAX_RW_COUNT) then MAX_RW_COUNT else count
  fileStartWrite f
  let fop ← fopsOf f.fOp
  let ret ← do
    if ← branch .vfsWriteHasWrite fop.write then fopWrite fid buf count f.fOp
    else if ← branch .vfsWriteHasWriteIter fop.writeIter then newSyncWrite fid buf count pos
    else pure (-EINVAL)
  if ← branch .vfsWritePositive (ret > 0) then pure ()  -- fsnotify_modify; add_wchar
  -- inc_syscw(current)
  fileEndWrite f
  return ret

/-- ksys_write (read_write.c:725-743) and SYSCALL_DEFINE3(write). -/
def ksysWrite (fd : Nat) (buf : ByteArray) (count : Nat) : FS.M Int := do
  let f ← fdgetPos fd
  let mut ret := -EBADF
  if ← branch .ksysWriteHasFile f.file.isSome then
    let some fid := f.file | invariant "unreachable"
    let ppos ← filePpos (← getFile fid)
    _ ← branch .ksysWriteHasPpos ppos.isSome
    ret ← vfsWrite fid buf count ppos
    if ← branch .ksysWriteRetNonneg (ret >= 0) then
      if ← branch .ksysWriteStorePos ppos.isSome then
        setFile fid { (← getFile fid) with fPos := ppos.getD 0 }
    fdputPos f
  return ret

end Leanux
