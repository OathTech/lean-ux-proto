import Leanux.Kernel.Refcount

/-!
# fs/eventfd.c — context and file operations

`eventfd_ctx_do_read`, `eventfd_read`, `eventfd_write`, `eventfd_release`,
`eventfd_ctx_put` and `eventfd_free_ctx`. Creation (`do_eventfd`) is in
`Leanux.FS.Eventfd`, which needs the descriptor table.

Every function runs with the C's locks as stated; lock acquire/release are
recorded in comments at the C's position. Wait-queue manipulation is a cut
point: the domain has no waiters, so `waitqueue_active` is false and a
waiter-present outcome is `unsupported`.
-/

namespace Leanux

/-- `struct kiocb`, the parts `eventfd_read` consults. -/
structure Kiocb where
  filp : FileId
  kiFlags : UInt32
  kiPos : Int

/-- `IOCB_NOWAIT` (include/linux/fs.h). -/
def IOCB_NOWAIT : UInt32 := 0x8   -- RWF_NOWAIT

/-- `file->private_data` of an eventfd file. -/
def eventfdCtxOf (file : File) : M CtxId :=
  match file.privateData with
  | some (.eventfdCtx id) => return id
  | none => invariant "eventfd operation on a file with NULL private_data"

/-- eventfd_free_ctx (eventfd.c:82-87). -/
def eventfdFreeCtx (id : CtxId) : M Unit := do
  let ctx ← getCtx id
  let some cid := ctx.id | invariant "eventfd_free_ctx reading an unset ctx->id"
  if ← branchCmp .eventfdFreeCtxHasId (cid >= 0) cid 0 then
    -- ida_free(&eventfd_ida, ctx->id)
    modifyK fun k => { k with idaUsed := k.idaUsed.erase cid.toNat }
  -- kfree(ctx)
  freeCtx id

/-- eventfd_ctx_put (eventfd.c:103-106): `kref_put(&ctx->kref, eventfd_free)`
    (include/linux/kref.h:62-69); `eventfd_free` is `container_of` plus
    `eventfd_free_ctx`. -/
def eventfdCtxPut (id : CtxId) : M Unit := do
  let ctx ← getCtx id
  setCtx id { ctx with kref := ctx.kref - 1 }
  if ← branch .krefPutLast (← refcountDecAndTest ctx.kref) then
    eventfdFreeCtx id

/-- eventfd_release (eventfd.c:109-116). `wake_up_poll(&ctx->wqh, EPOLLHUP)`
    is a cut point: with no waiters it changes no mirror state. -/
def eventfdRelease (fid : FileId) : M Int := do
  let file ← getFile fid
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  let ctx ← getCtx id
  if ctx.waiters != 0 then unsupported "wake_up_poll with waiters"
  eventfdCtxPut id
  return 0

/-- eventfd_ctx_do_read (eventfd.c:176-182), called with `ctx->wqh.lock` held:
    `*cnt = ((ctx->flags & EFD_SEMAPHORE) && ctx->count) ? 1 : ctx->count;`
    then `ctx->count -= *cnt;` — two statements, two mirror updates. -/
def eventfdCtxDoRead (id : CtxId) : M UInt64 := do
  let ctx ← getCtx id
  let one ← do
    if ← branchCmp .ctxDoReadSemaphore (hasFlag ctx.flags EFD_SEMAPHORE) (ctx.flags &&& EFD_SEMAPHORE).toNat 0 then
      branch .ctxDoReadCountNonzero (ctx.count != 0)  -- a branch-free select: no comparison
    else pure false
  let cnt := if one then 1 else ctx.count
  setCtx id { ctx with count := ctx.count - cnt }
  return cnt

/-- eventfd_read (eventfd.c:214-245), the `read_iter` operation. `iterCount`
    is `iov_iter_count(to)`; the destination buffer is the caller's. -/
def eventfdRead (iocb : Kiocb) (iterCount : Nat) : M Int := do
  let file ← getFile iocb.filp
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  if ← branchCmp .eventfdReadShort (iterCount < 8) iterCount 8 then return -EINVAL
  -- spin_lock_irq(&ctx->wqh.lock)
  if ← branchCmp .eventfdReadEmpty ((← getCtx id).count == 0) (← getCtx id).count.toNat 0 then
    if ← branchCmp .eventfdReadNonblock (hasFlag file.fFlags O_NONBLOCK) (file.fFlags &&& O_NONBLOCK).toNat 0 then
      return -EAGAIN  -- spin_unlock_irq
    if ← branch .eventfdReadNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) then
      return -EAGAIN  -- spin_unlock_irq
    unsupported "eventfd_read blocking wait"
  let ucnt ← eventfdCtxDoRead id
  modifyK fun k => { k with task := { k.task with inEventfd := true } }
  if ← branch .eventfdReadWaitqueueActive ((← getCtx id).waiters != 0) then
    unsupported "wake_up_locked_poll with waiters"
  modifyK fun k => { k with task := { k.task with inEventfd := false } }
  -- spin_unlock_irq(&ctx->wqh.lock)
  -- `copy_to_iter`: the guest's buffer is mapped (a trace input under A-U, 6.5)
  if ← branch .eventfdReadCopyFault false then return -EFAULT
  modify fun w => { w with userOut := some ucnt }
  return 8

/-- eventfd_write (eventfd.c:247-280), the `write` operation. `userWord` is
    the 8-byte value in the caller's buffer. -/
def eventfdWrite (fid : FileId) (userWord : UInt64) (count : Nat) : M Int := do
  let file ← getFile fid
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  if ← branchCmp .eventfdWriteWrongSize (count != 8) count 8 then return -EINVAL
  -- `copy_from_user`: the guest's buffer is mapped (A-U, 6.5)
  if ← branch .eventfdWriteCopyFault false then return -EFAULT
  let ucnt := userWord
  if ← branchCmp .eventfdWriteReserved (ucnt == ULLONG_MAX) ucnt.toNat ULLONG_MAX.toNat then return -EINVAL
  -- spin_lock_irq(&ctx->wqh.lock)
  let mut res : Int := -EAGAIN
  if ← branchCmp .eventfdWriteFits (ULLONG_MAX - (← getCtx id).count > ucnt) (ULLONG_MAX - (← getCtx id).count).toNat ucnt.toNat then
    res := 8
  else if ← branchCmp .eventfdWriteBlocking (!hasFlag file.fFlags O_NONBLOCK) (file.fFlags &&& O_NONBLOCK).toNat 0 then
    unsupported "eventfd_write blocking wait"
  if ← branch .eventfdWriteResPositive (res > 0) then
    let ctx ← getCtx id
    setCtx id { ctx with count := ctx.count + ucnt }
    modifyK fun k => { k with task := { k.task with inEventfd := true } }
    if ← branch .eventfdWriteWaitqueueActive ((← getCtx id).waiters != 0) then
      unsupported "wake_up_locked_poll with waiters"
    modifyK fun k => { k with task := { k.task with inEventfd := false } }
  -- spin_unlock_irq(&ctx->wqh.lock)
  return res

/-! ## `f_op` dispatch (a cut point: indirect calls through `file->f_op`)

`file->f_op` names the operations table; this is the relation a later proof
would state as `f_op == &eventfd_fops ⇔ fOp = some .eventfd`. Fixture files use
operations outside the slice, so asking for them is `unsupported`; a NULL
`f_op` on these paths is a mirror defect. -/

/-- The members of `struct file_operations` these paths test. -/
structure Fops where
  owner : Bool := false
  llseek : Bool := false
  read : Bool := false
  readIter : Bool := false
  write : Bool := false
  writeIter : Bool := false
  flush : Bool := false
  release : Bool := false
  fasync : Bool := false
  checkFlags : Bool := false
  iterateShared : Bool := false

/-- `eventfd_fops` (eventfd.c:302-311): release, poll, read_iter, write,
    llseek = noop_llseek, show_fdinfo; built in, so no module owner. -/
def eventfdFops : Fops :=
  { llseek := true, readIter := true, write := true, release := true }

def fopsOf : Option FopsId → M Fops
  | some .eventfd => return eventfdFops
  | some (.fixture name) => unsupported s!"file operations of fixture file {name}"
  | none => invariant "file->f_op is NULL"

def fopRelease (fid : FileId) : Option FopsId → M Int
  | some .eventfd => eventfdRelease fid
  | some (.fixture name) => unsupported s!"release of fixture file {name}"
  | none => invariant "file->f_op is NULL"

def fopReadIter (iocb : Kiocb) (count : Nat) : Option FopsId → M Int
  | some .eventfd => eventfdRead iocb count
  | some (.fixture name) => unsupported s!"read_iter of fixture file {name}"
  | none => invariant "file->f_op is NULL"

def fopWrite (fid : FileId) (userWord : UInt64) (count : Nat) : Option FopsId → M Int
  | some .eventfd => eventfdWrite fid userWord count
  | some (.fixture name) => unsupported s!"write of fixture file {name}"
  | none => invariant "file->f_op is NULL"

end Leanux
