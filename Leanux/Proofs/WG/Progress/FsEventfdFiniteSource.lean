import Leanux.Proofs.WG.Progress.FsDescriptorFiniteSource
import Leanux.Proofs.WG.Progress.FsAnonymousFiniteSource
import Leanux.FS.Eventfd

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! The original eventfd2 path with concrete finite allocation callbacks.
All errno, unsupported, invariant and cleanup paths retain their order. -/

def doEventfd (count : UInt32) (flags : UInt32) : FS.M Int := do
  if ← branchCmp .doEventfdInvalidFlags (flags &&& ~~~EFD_FLAGS_SET != 0) (flags &&& ~~~EFD_FLAGS_SET).toNat 0 then return -EINVAL
  -- ctx = kmalloc(sizeof(*ctx), GFP_KERNEL)
  if ← branch .doEventfdNoMem (!(← (monadLift (hiddenAllocFinite .kmallocEventfdCtx)))) then return -ENOMEM
  let cid := (← get).nextCtx
  -- kref_init; init_waitqueue_head; ctx->count = count; ctx->flags = flags
  setCtx cid { kref := 1, count := count.toUInt64, flags, id := none }
  modify fun k => { k with nextCtx := cid + 1 }
  let id ← idaAlloc  -- ctx->id = ida_alloc(...): stored unchecked, as in the C
  setCtx cid { (← getCtx cid) with id := some id }
  let flags := (flags &&& EFD_SHARED_FCNTL_FLAGS) ||| O_RDWR
  let fd ← getUnusedFdFlags flags
  if ← branchCmp .doEventfdFdError (fd < 0) fd 0 then
    eventfdFreeCtx cid  -- err:
    return fd
  let file ← anonInodeGetfile .eventfd (.eventfdCtx cid) flags
  if ← branch .doEventfdFileError (file matches .error _) then
    putUnusedFd fd.toNat
    eventfdFreeCtx cid  -- err:
    return match file with | .error e => e | .ok _ => 0
  let .ok fid := file | invariant "unreachable"
  let f ← getFile fid
  setFile fid { f with fMode := f.fMode ||| FMODE_NOWAIT }
  fdInstall fd.toNat fid
  return fd

theorem doEventfd_source (count flags : UInt32) :
    Leanux.doEventfd count flags = doEventfd count flags := by
  unfold Leanux.doEventfd doEventfd
  simp only [hiddenAlloc, hiddenAlloc_finite_source, getUnusedFdFlags_source, anonInodeGetfile_source]
  rfl

def sysEventfd2 (count flags : UInt32) : FS.M Int := doEventfd count flags

theorem sysEventfd2_source (count flags : UInt32) :
    Leanux.sysEventfd2 count flags = sysEventfd2 count flags := by
  unfold Leanux.sysEventfd2 sysEventfd2
  simp only [doEventfd_source]


end Leanux.Proofs.WG.Progress.FsFinite
