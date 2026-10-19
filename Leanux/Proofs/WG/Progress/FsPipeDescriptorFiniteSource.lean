import Leanux.Proofs.WG.Progress.FsPipeCreationFiniteSource
import Leanux.Proofs.WG.Progress.FsDescriptorFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! The original descriptor-pair creation and pipe2 caller, with finite
file/descriptor callbacks and every original rollback and Stop. -/

def doPipeFlags (flags : UInt32) : FS.M (Except Int (Nat × Nat × FileId × FileId)) := do
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

theorem doPipeFlags_source (flags : UInt32) :
    Leanux.doPipeFlags flags = doPipeFlags flags := by
  unfold Leanux.doPipeFlags doPipeFlags
  simp only [createPipeFiles_source, getUnusedFdFlags_source]
  rfl

def doPipe2 (flags : UInt32) : FS.M Int := do
  let r ← doPipeFlags flags
  let error : Int := match r with | .error e => e | .ok _ => 0
  if ← branch .doPipe2Ok (error == 0) then
    let .ok (fdr, fdw, f0, f1) := r | invariant "unreachable"
    -- `copy_to_user`: the guest's buffer is mapped (a trace input, A-U, 6.5)
    if ← branch .doPipe2CopyFault false then
      fput f0
      fput f1
      putUnusedFd fdr
      putUnusedFd fdw
      return -EFAULT
    modify fun w => { w with userFds := some (fdr, fdw) }
    fdInstall fdr f0
    fdInstall fdw f1
  return error

theorem doPipe2_source (flags : UInt32) :
    Leanux.doPipe2 flags = doPipe2 flags := by
  unfold Leanux.doPipe2 doPipe2
  simp only [doPipeFlags_source]
  rfl

def sysPipe2 (flags : UInt32) : FS.M Int := doPipe2 flags

theorem sysPipe2_source (flags : UInt32) :
    Leanux.sysPipe2 flags = sysPipe2 flags := by
  unfold Leanux.sysPipe2 sysPipe2
  simp only [doPipe2_source]


end Leanux.Proofs.WG.Progress.FsFinite
