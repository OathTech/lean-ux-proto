import Leanux.Proofs.WG.Progress.FsPipeCallerFiniteSource
import Leanux.FS.ReadWrite
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Complete read/write callers use the finite iterator bodies. Descriptor
lookup/payment, position updates and refusal order remain the native ones. -/

def newSyncRead (fid : FileId) (len : Nat) (ppos : Option Int) : FS.M (Int × Option Int) := do
  let f ← getFile fid
  let iocb : Kiocb := { filp := fid, kiFlags := f.fIocbFlags, kiPos := ppos.getD 0 }
  let ret ← fopReadIter iocb len f.fOp
  if ← branch .newSyncReadQueued (ret == -529) then  -- BUG_ON(ret == -EIOCBQUEUED)
    unsupported "new_sync_read: -EIOCBQUEUED"
  -- if (ppos) *ppos = kiocb.ki_pos; eventfd_read leaves ki_pos unchanged
  return (ret, ppos.map fun _ => iocb.kiPos)

theorem newSyncRead_source (fid : FileId) (len : Nat) (ppos : Option Int) :
    Leanux.newSyncRead fid len ppos = newSyncRead fid len ppos := by
  unfold Leanux.newSyncRead newSyncRead
  simp only [fopReadIter_source] <;> rfl

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

theorem vfsRead_source (fid : FileId) (count : Nat) (pos : Option Int) :
    Leanux.vfsRead fid count pos = vfsRead fid count pos := by
  unfold Leanux.vfsRead vfsRead
  simp only [newSyncRead_source] <;> rfl

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

theorem ksysRead_source (fd : Nat) (count : Nat) :
    Leanux.ksysRead fd count = ksysRead fd count := by
  unfold Leanux.ksysRead ksysRead
  simp only [vfsRead_source] <;> rfl

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

theorem newSyncWrite_source (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) :
    Leanux.newSyncWrite fid buf len ppos = newSyncWrite fid buf len ppos := by
  unfold Leanux.newSyncWrite newSyncWrite
  simp only [fopWriteIter_source] <;> rfl

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

theorem vfsWrite_source (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) :
    Leanux.vfsWrite fid buf count pos = vfsWrite fid buf count pos := by
  unfold Leanux.vfsWrite vfsWrite
  simp only [newSyncWrite_source] <;> rfl

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

theorem ksysWrite_source (fd : Nat) (buf : ByteArray) (count : Nat) :
    Leanux.ksysWrite fd buf count = ksysWrite fd buf count := by
  unfold Leanux.ksysWrite ksysWrite
  simp only [vfsWrite_source] <;> rfl

end Leanux.Proofs.WG.Progress.FsFinite
