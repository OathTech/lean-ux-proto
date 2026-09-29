import Leanux.FS.File
import Leanux.FS.AnonInodes

/-!
# fs/eventfd.c — `do_eventfd` and the `eventfd2` syscall
-/

namespace Leanux

/-- `ida_alloc(&eventfd_ida, GFP_KERNEL)` (lib/idr.c): a cut point with
    contract "least unused id ≥ 0, or -ENOMEM" (an environment choice). -/
def idaAlloc : M Int := do
  if !(← envOk .idaAlloc) then return -ENOMEM
  let k ← getK
  let id := (List.range (k.idaUsed.size + 1)).find? (fun n => !k.idaUsed.contains n) |>.getD (k.idaUsed.size + 1)
  modifyK fun k => { k with idaUsed := k.idaUsed.insert id }
  return id

/-- do_eventfd (eventfd.c:379-423). -/
def doEventfd (count : UInt32) (flags : UInt32) : M Int := do
  if ← branchCmp .doEventfdInvalidFlags (flags &&& ~~~EFD_FLAGS_SET != 0) (flags &&& ~~~EFD_FLAGS_SET).toNat 0 then return -EINVAL
  -- ctx = kmalloc(sizeof(*ctx), GFP_KERNEL)
  if ← branch .doEventfdNoMem (!(← envOk .kmallocEventfdCtx)) then return -ENOMEM
  let cid := (← getK).nextCtx
  -- kref_init; init_waitqueue_head; ctx->count = count; ctx->flags = flags
  setCtx cid { kref := 1, count := count.toUInt64, flags, id := none }
  modifyK fun k => { k with nextCtx := cid + 1 }
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

/-- SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags) (eventfd.c:425-428). -/
def sysEventfd2 (count flags : UInt32) : M Int := doEventfd count flags

end Leanux
