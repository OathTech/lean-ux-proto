import Leanux.Proofs.WG.Progress.PipeRoundupSource
import Leanux.FS.Fcntl
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Finite rounding replaces only the unbounded pure doubling loop. Original
resize accounting, bounded copying, wakeups and fcntl dispatch are unchanged. -/

def roundPipeSize (size : Nat) : FS.M Nat := do
  if ← branchCmp .roundPipeSizeTooBig (size > 2 ^ 31) size (2 ^ 31) then return 0
  -- Minimum pipe size, as required by POSIX
  if ← branchCmp .roundPipeSizeSmall (size < PAGE_SIZE) size PAGE_SIZE then return PAGE_SIZE
  return (PipeRoundup.finite size).getD 0

theorem roundPipeSize_source (size : Nat) :
    Leanux.roundPipeSize size = roundPipeSize size := by
  unfold Leanux.roundPipeSize roundPipeSize
  rw [(PipeRoundup.finite_source size).1]
  rfl

def pipeSetSize (pid : PipeId) (arg : Nat) : FS.M Int := do
  -- pipe_has_watch_queue(pipe) is the constant false (1341)
  let size ← roundPipeSize arg
  let nrSlots := size >>> 12  -- size >> PAGE_SHIFT
  if ← branchCmp .pipeSetSizeZero (nrSlots == 0) nrSlots 0 then return -EINVAL
  -- `nr_slots > pipe->max_usage && size > pipe_max_size && !capable(CAP_SYS_RESOURCE)`
  let p ← getPipe pid
  let maxSize := (← get).pipeMaxSize
  let eperm ← do
    if ← branchCmp .pipeSetSizeGrowMax (nrSlots > p.maxUsage) nrSlots p.maxUsage then
      if ← branchCmp .pipeSetSizeOverMax (size > maxSize) size maxSize then
        branch .pipeSetSizeNotCapable false  -- capable(): root
      else pure false
    else pure false
  if eperm then return -EPERM
  let userBufs ← accountPipeBuffers p.nrAccounted nrSlots
  -- `nr_slots > pipe->max_usage && (too_many_pipe_buffers_hard(user_bufs) ||
  --  too_many_pipe_buffers_soft(user_bufs)) && pipe_is_unprivileged_user()`
  let limited ← do
    if ← branchCmp .pipeSetSizeGrowLimits (nrSlots > p.maxUsage) nrSlots p.maxUsage then
      let over ← do
        if ← branch .pipeSetSizeHard (← tooManyPipeBuffersHard userBufs) then pure true
        else branch .pipeSetSizeSoft (← tooManyPipeBuffersSoft userBufs)
      if over then branch .pipeSetSizeUnpriv (← pipeIsUnprivilegedUser) else pure false
    else pure false
  -- out_revert_acct (1377-1378) on both error paths; the success path returns
  -- `pipe->max_usage * PAGE_SIZE` from inside the happy path (1373), with the
  -- accounting kept
  let outRevertAcct : FS.M Unit := do
    _ ← accountPipeBuffers nrSlots (← getPipe pid).nrAccounted
  if limited then
    outRevertAcct
    return -EPERM
  let ret ← pipeResizeRing pid nrSlots
  if ← branchCmp .pipeSetSizeResizeErr (ret < 0) ret 0 then
    outRevertAcct
    return ret
  return ((← getPipe pid).maxUsage * PAGE_SIZE : Nat)

theorem pipeSetSize_source (pid : PipeId) (arg : Nat) :
    Leanux.pipeSetSize pid arg = pipeSetSize pid arg := by
  unfold Leanux.pipeSetSize pipeSetSize
  simp only [roundPipeSize_source] <;> rfl

def pipeFcntl (fid : FileId) (cmd : Nat) (arg : Nat) : FS.M Int := do
  let pipe? ← getPipeInfo (← getFile fid)
  if ← branch .pipeFcntlNoPipe pipe?.isNone then return -EBADF
  let some pid := pipe? | invariant "unreachable"
  -- mutex_lock(&pipe->mutex); switch (cmd)
  let ret ← do
    if cmd == F_SETPIPE_SZ then
      _ ← branch .pipeFcntlSetSize true
      pipeSetSize pid arg
    else if cmd == F_GETPIPE_SZ then
      _ ← branch .pipeFcntlGetSize true
      pure ((← getPipe pid).maxUsage * PAGE_SIZE : Nat)
    else invariant s!"pipe_fcntl: do_fcntl does not route command {cmd} here"
  -- mutex_unlock(&pipe->mutex)
  return ret

theorem pipeFcntl_source (fid : FileId) (cmd : Nat) (arg : Nat) :
    Leanux.pipeFcntl fid cmd arg = pipeFcntl fid cmd arg := by
  unfold Leanux.pipeFcntl pipeFcntl
  simp only [pipeSetSize_source] <;> rfl

def doFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) : FS.M Int := do
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

theorem doFcntl_source (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) :
    Leanux.doFcntl fd cmd arg fid = doFcntl fd cmd arg fid := by
  unfold Leanux.doFcntl doFcntl
  simp only [pipeFcntl_source] <;> rfl

def sysFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) : FS.M Int := do
  let f ← fdgetRaw fd
  let mut err := -EBADF
  if ← branch .fcntlNoFile f.file.isNone then return err  -- goto out
  let some fid := f.file | invariant "unreachable"
  if ← branchCmp .fcntlPathFile (hasFlag (← getFile fid).fMode FMODE_PATH) ((← getFile fid).fMode &&& FMODE_PATH).toNat 0 then
    unsupported "check_fcntl_cmd for O_PATH files"
  err ← doFcntl fd cmd arg fid
  fdput f  -- out1:
  return err

theorem sysFcntl_source (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    Leanux.sysFcntl fd cmd arg = sysFcntl fd cmd arg := by
  unfold Leanux.sysFcntl sysFcntl
  simp only [doFcntl_source] <;> rfl

end Leanux.Proofs.WG.Progress.FsFinite
