import Leanux.Proofs.WG.Progress.FsDescriptorFiniteSource
import Leanux.Proofs.WG.Progress.FsReleaseFiniteSource
import Leanux.FS.Close

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Descriptor duplication and synchronous close with finite allocation
and final-release callbacks. Native error and cleanup order is unchanged. -/

def ksysDup3 (oldfd newfd : Nat) (flags : UInt32) : FS.M Int := do
  if ← branchCmp .dup3InvalidFlags (flags &&& ~~~O_CLOEXEC != 0) (flags &&& ~~~O_CLOEXEC).toNat 0 then return -EINVAL
  if ← branchCmp .dup3Equal (oldfd == newfd) oldfd newfd then return -EINVAL
  if ← branchCmp .dup3TargetLimit (newfd >= (← getTask .task).rlimitNofile) newfd (← getTask .task).rlimitNofile then return -EBADF
  -- spin_lock(&files->file_lock)
  let err ← expandFiles newfd
  let file ← filesLookupFdRaw oldfd   -- files_lookup_fd_locked
  if ← branch .dup3NoFile file.isNone then return -EBADF  -- Ebadf: spin_unlock
  if ← branchCmp .dup3ExpandError (err < 0) err 0 then
    if ← branch .dup3ExpandEmfile (err == -EMFILE) then return -EBADF
    return err  -- out_unlock
  match file with
  | some fid => doDup2 fid newfd flags
  | none => invariant "unreachable: file checked non-NULL"

theorem ksysDup3_source (oldfd newfd : Nat) (flags : UInt32) :
    Leanux.ksysDup3 oldfd newfd flags = ksysDup3 oldfd newfd flags := by
  unfold Leanux.ksysDup3 ksysDup3
  simp only [expandFiles_source] <;> rfl

def sysDup (fildes : Nat) : FS.M Int := do
  let file ← fgetRaw fildes
  let mut ret := -EBADF
  if ← branch .dupFound file.isSome then
    let some fid := file | invariant "unreachable"
    ret ← getUnusedFdFlags 0
    if ← branchCmp .dupAllocOk (ret >= 0) ret 0 then fdInstall ret.toNat fid
    else fput fid
  return ret

theorem sysDup_source (fildes : Nat) :
    Leanux.sysDup fildes = sysDup fildes := by
  unfold Leanux.sysDup sysDup
  simp only [getUnusedFdFlags_source] <;> rfl

def sysClose (fd : Nat) : FS.M Int := do
  let file ← fileCloseFd fd
  if ← branch .closeNoFile file.isNone then return -EBADF
  let some fid := file | invariant "unreachable"
  let retval ← filpFlush fid
  -- "We're returning to user space. Don't bother with any delayed fput() cases."
  fputSync fid
  -- `unlikely(retval == -ERESTARTSYS || retval == -ERESTARTNOINTR ||
  --          retval == -ERESTARTNOHAND || retval == -ERESTART_RESTARTBLOCK)`
  let restart ← do
    if ← branch .closeRestartSys (retval == -512) then pure true
    else if ← branch .closeRestartNoIntr (retval == -513) then pure true
    else if ← branch .closeRestartNoHand (retval == -514) then pure true
    else branch .closeRestartBlock (retval == -516)
  if restart then return -4  -- -EINTR
  return retval

theorem sysClose_source (fd : Nat) :
    Leanux.sysClose fd = sysClose fd := by
  unfold Leanux.sysClose sysClose
  simp only [fputSync_source] <;> rfl


end Leanux.Proofs.WG.Progress.FsFinite
