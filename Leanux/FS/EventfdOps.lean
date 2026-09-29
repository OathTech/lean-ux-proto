import Leanux.Kernel.Defs

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

/-- eventfd_free_ctx (eventfd.c:82-87). -/
def eventfdFreeCtx (id : CtxId) : M Unit := do
  let ctx ← getCtx id
  let some cid := ctx.id | unsupported "eventfd_free_ctx reading an unset ctx->id"
  if ← branch .eventfdFreeCtxHasId (cid >= 0) then
    -- ida_free(&eventfd_ida, ctx->id)
    modifyK fun k => { k with idaUsed := fun n => if n = cid.toNat then false else k.idaUsed n }
  -- kfree(ctx)
  modifyK fun k => { k with ctxs := fun n => if n = id then none else k.ctxs n }

/-- `refcount_dec_and_test` = `__refcount_sub_and_test(1, r, NULL)`
    (include/linux/refcount.h:262-278). `if (oldp)` is constant-folded away
    (NULL); saturation reports are `unsupported`. -/
def refcountDecAndTest (old : Nat) : M Bool := do
  let i := 1
  if ← branch .refcountSubPositive (old > 0) then
    if ← branch .refcountSubToZero (old == i) then return true
  if ← branch .refcountSubNonpositive (old == 0) then unsupported "refcount_warn_saturate (use after free)"
  if ← branch .refcountSubUnderflow (old < i) then unsupported "refcount_warn_saturate (underflow)"
  return false

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
  let .eventfd id := file.kind | unsupported "eventfd_release on a non-eventfd file"
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
    if ← branch .ctxDoReadSemaphore (hasFlag ctx.flags EFD_SEMAPHORE) then
      branch .ctxDoReadCountNonzero (ctx.count != 0)
    else pure false
  let cnt := if one then 1 else ctx.count
  setCtx id { ctx with count := ctx.count - cnt }
  return cnt

/-- eventfd_read (eventfd.c:214-245), the `read_iter` operation. `iterCount`
    is `iov_iter_count(to)`; the destination buffer is the caller's. -/
def eventfdRead (iocb : Kiocb) (iterCount : Nat) : M Int := do
  let file ← getFile iocb.filp
  let .eventfd id := file.kind | unsupported "eventfd_read on a non-eventfd file"
  if ← branch .eventfdReadShort (iterCount < 8) then return -EINVAL
  -- spin_lock_irq(&ctx->wqh.lock)
  if ← branch .eventfdReadEmpty ((← getCtx id).count == 0) then
    if ← branch .eventfdReadNonblock (hasFlag file.fFlags O_NONBLOCK) then
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
  if ← branch .eventfdReadCopyFault (!(← envOk .copyToUser)) then return -EFAULT
  modify fun w => { w with userOut := some ucnt }
  return 8

/-- eventfd_write (eventfd.c:247-280), the `write` operation. `userWord` is
    the 8-byte value in the caller's buffer. -/
def eventfdWrite (fid : FileId) (userWord : UInt64) (count : Nat) : M Int := do
  let file ← getFile fid
  let .eventfd id := file.kind | unsupported "eventfd_write on a non-eventfd file"
  if ← branch .eventfdWriteWrongSize (count != 8) then return -EINVAL
  if ← branch .eventfdWriteCopyFault (!(← envOk .copyFromUser)) then return -EFAULT
  let ucnt := userWord
  if ← branch .eventfdWriteReserved (ucnt == ULLONG_MAX) then return -EINVAL
  -- spin_lock_irq(&ctx->wqh.lock)
  let mut res : Int := -EAGAIN
  if ← branch .eventfdWriteFits (ULLONG_MAX - (← getCtx id).count > ucnt) then
    res := 8
  else if ← branch .eventfdWriteBlocking (!hasFlag file.fFlags O_NONBLOCK) then
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

The file's kind fixes its operations table; this is the relation a later
proof would state as `f_op == &eventfd_fops ⇔ kind = eventfd`. Fixture files
use operations outside the slice, so asking for them is `unsupported`. -/

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
  iterateShared : Bool := false

/-- `eventfd_fops` (eventfd.c:302-311): release, poll, read_iter, write,
    llseek = noop_llseek, show_fdinfo; built in, so no module owner. -/
def eventfdFops : Fops :=
  { llseek := true, readIter := true, write := true, release := true }

def fopsOf : FileKind → M Fops
  | .eventfd _ => return eventfdFops
  | .fixture name => unsupported s!"file operations of fixture file {name}"

def fopRelease (fid : FileId) : FileKind → M Int
  | .eventfd _ => eventfdRelease fid
  | .fixture name => unsupported s!"release of fixture file {name}"

def fopReadIter (iocb : Kiocb) (count : Nat) : FileKind → M Int
  | .eventfd _ => eventfdRead iocb count
  | .fixture name => unsupported s!"read_iter of fixture file {name}"

def fopWrite (fid : FileId) (userWord : UInt64) (count : Nat) : FileKind → M Int
  | .eventfd _ => eventfdWrite fid userWord count
  | .fixture name => unsupported s!"write of fixture file {name}"

end Leanux
