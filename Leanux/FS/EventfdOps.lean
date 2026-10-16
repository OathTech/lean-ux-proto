import Leanux.Kernel.Refcount
import Leanux.FS.Pipe

/-!
# fs/eventfd.c — context and file operations

`eventfd_ctx_do_read`, `eventfd_read`, `eventfd_write`, `eventfd_release`,
`eventfd_poll`, `eventfd_ctx_put` and `eventfd_free_ctx`, and the `f_op`
dispatchers of the slice (`vfs_poll` among them). Creation (`do_eventfd`) is
in `Leanux.FS.Eventfd`, which needs the descriptor table.

Every function runs with the C's locks as stated; lock acquire/release are
recorded in comments at the C's position. The wake-ups are calls into the
wait-queue service (`Leanux.FS.Wait`) walking `ctx->wqh`, and `eventfd_poll`
registers on it through `poll_wait` (docs/2026-10-12-epoll-design.md, 2.5,
4.2, 4.6).
-/

namespace Leanux

/-- `file->private_data` of an eventfd file. -/
def eventfdCtxOf (file : File) : M CtxId :=
  match file.privateData with
  | some (.eventfdCtx id) => return id
  | some (.pipe _) => invariant "eventfd operation on a pipe file"
  | some (.eventpoll _) => invariant "eventfd operation on an epoll file"
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

/-- eventfd_release (eventfd.c:109-116). By the time it runs, `__fput` has
    already called `eventpoll_release`, which removes every epoll item on the
    file, so `wake_up_poll` walks an empty queue (design 2.5, 2.8). -/
def eventfdRelease (fid : FileId) : M Int := do
  let file ← getFile fid
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  wakeUpPoll (.eventfdWqh id) EPOLLHUP
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
  modifyTask .task fun t => { t with inEventfd := true }
  if ← branch .eventfdReadWaitqueueActive (← waitqueueActive (.eventfdWqh id)) then
    wakeUpLockedPoll (.eventfdWqh id) EPOLLOUT
  modifyTask .task fun t => { t with inEventfd := false }
  -- spin_unlock_irq(&ctx->wqh.lock)
  -- `copy_to_iter`: the guest's buffer is mapped (a trace input under A-U, 6.5)
  if ← branch .eventfdReadCopyFault false then return -EFAULT
  -- copy_to_iter(&ucnt, sizeof(ucnt), to): the 8 bytes, little-endian
  modify fun w => { w with userOut := some (ByteArray.mk ((List.range 8).map fun k =>
    UInt8.ofNat (ucnt.toNat / 256 ^ k % 256)).toArray) }
  return 8

/-- eventfd_write (eventfd.c:247-280), the `write` operation. `buf` is the
    caller's buffer. -/
def eventfdWrite (fid : FileId) (buf : ByteArray) (count : Nat) : M Int := do
  let file ← getFile fid
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  if ← branchCmp .eventfdWriteWrongSize (count != 8) count 8 then return -EINVAL
  -- `copy_from_user`: the guest's buffer is mapped (A-U, 6.5)
  if ← branch .eventfdWriteCopyFault false then return -EFAULT
  -- copy_from_user(&ucnt, buf, sizeof(ucnt)): the first 8 bytes, little-endian
  if buf.size < 8 then invariant "eventfd_write: the caller's buffer is shorter than 8 bytes"
  let ucnt : UInt64 := UInt64.ofNat ((List.range 8).foldr (fun k acc => acc * 256 + buf[k]!.toNat) 0)
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
    modifyTask .task fun t => { t with inEventfd := true }
    if ← branch .eventfdWriteWaitqueueActive (← waitqueueActive (.eventfdWqh id)) then
      wakeUpLockedPoll (.eventfdWqh id) EPOLLIN
    modifyTask .task fun t => { t with inEventfd := false }
  -- spin_unlock_irq(&ctx->wqh.lock)
  return res

/-- eventfd_poll (eventfd.c:118-174), the `poll` operation: registers on
    `ctx->wqh`, then reads `count` outside the lock (the comment at 126-162
    argues the order is safe; one task here). -/
def eventfdPoll (fid : FileId) (wait : PollTable) : M UInt32 := do
  let file ← getFile fid
  let id ← eventfdCtxOf file  -- ctx = file->private_data
  pollWait fid (.eventfdWqh id) wait
  -- count = READ_ONCE(ctx->count)
  let count := (← getCtx id).count
  let mut events : UInt32 := 0
  if ← branchCmp .eventfdPollCountPositive (count > 0) count.toNat 0 then
    events := events ||| EPOLLIN
  -- the two tests below are threaded away by the built code when `count > 0`
  -- was false (count is then 0): no operands
  if ← branch .eventfdPollCountMax (count == ULLONG_MAX) then
    events := events ||| EPOLLERR
  if ← branch .eventfdPollRoom (ULLONG_MAX - 1 > count) then
    events := events ||| EPOLLOUT
  return events

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
  poll : Bool := false
  unlockedIoctl : Bool := false
  «open» : Bool := false
  spliceWrite : Bool := false

/-- `eventfd_fops` (eventfd.c:302-311): release, poll, read_iter, write,
    llseek = noop_llseek, show_fdinfo; built in, so no module owner. -/
def eventfdFops : Fops :=
  { llseek := true, readIter := true, write := true, release := true, poll := true }

/-- `pipefifo_fops` (fs/pipe.c:1232-1241): open, read_iter, write_iter,
    poll, unlocked_ioctl, release, fasync, splice_write; no `llseek` (so no
    `FMODE_LSEEK`), no `check_flags`; built in. -/
def pipefifoFops : Fops :=
  { readIter := true, writeIter := true, release := true, fasync := true, poll := true,
    unlockedIoctl := true, «open» := true, spliceWrite := true }

/-- `eventpoll_fops` (fs/eventpoll.c:1271-1280): release,
    poll, llseek = noop_llseek, unlocked_ioctl, compat_ioctl, show_fdinfo;
    built in. -/
def eventpollFops : Fops :=
  { llseek := true, release := true, poll := true, unlockedIoctl := true }

def fopsOf : Option FopsId → M Fops
  | some .eventfd => return eventfdFops
  | some .pipefifo => return pipefifoFops
  | some .eventpoll => return eventpollFops
  -- W8: a fixture socket's socket_file_ops has a release (sock_close); the
  -- pin's ns_file_operations has none (the namespace goes with the dentry)
  | some (.fixture name) => return { release := name != "netns-pin" }
  | none => invariant "file->f_op is NULL"

-- `fopRelease`, the `f_op->release` dispatcher, is in `Leanux.FS.Fput` with
-- `__fput`: the eventpoll arm needs the epoll mirror, which follows this
-- module (stream S).

def fopReadIter (iocb : Kiocb) (count : Nat) : Option FopsId → M Int
  | some .eventfd => eventfdRead iocb count
  | some .pipefifo => pipeRead iocb count
  | some .eventpoll => invariant "eventpoll_fops has no read_iter (FMODE_CAN_READ is never set)"
  | some (.fixture name) => unsupported s!"read_iter of fixture file {name}"
  | none => invariant "file->f_op is NULL"

def fopWrite (fid : FileId) (buf : ByteArray) (count : Nat) : Option FopsId → M Int
  | some .eventfd => eventfdWrite fid buf count
  | some .pipefifo => invariant "pipefifo_fops has no write (fopsOf routes it to write_iter)"
  | some .eventpoll => invariant "eventpoll_fops has no write (FMODE_CAN_WRITE is never set)"
  | some (.fixture name) => unsupported s!"write of fixture file {name}"
  | none => invariant "file->f_op is NULL"

/-- `f_op->write_iter` (the `new_sync_write` path). `from` is the caller's
    buffer as an `iov_iter`. -/
def fopWriteIter (iocb : Kiocb) («from» : IovIter) : Option FopsId → M Int
  | some .pipefifo => pipeWrite iocb «from»
  | some .eventfd => invariant "eventfd_fops has no write_iter (fopsOf routes it to write)"
  | some .eventpoll => invariant "eventpoll_fops has no write_iter (FMODE_CAN_WRITE is never set)"
  | some (.fixture name) => unsupported s!"write_iter of fixture file {name}"
  | none => invariant "file->f_op is NULL"

/-- `f_op->poll(file, pt)`. An epoll file's `ep_eventpoll_poll` is reached
    through `vfs_poll` only from `select`/`poll` (outside the domain):
    `ep_item_poll` dispatches an epoll target to `__ep_eventpoll_poll`
    itself (fs/eventpoll.c:1233-1236), in `Leanux.FS.Eventpoll`. -/
def fopPoll (fid : FileId) (pt : PollTable) : Option FopsId → M UInt32
  | some .eventfd => eventfdPoll fid pt
  | some .pipefifo => pipePoll fid pt
  | some .eventpoll => unsupported "ep_eventpoll_poll through vfs_poll (select/poll on an epoll file)"
  | some (.fixture name) => unsupported s!"poll of fixture file {name}"
  | none => invariant "file->f_op is NULL"

/-- vfs_poll (include/linux/poll.h:88-93), reached from `ep_item_poll`
    (fs/eventpoll.c:1234). A fixture file's `f_op` is modelled for release
    only (`fopsOf`), so its poll stops before the test. The
    `DEFAULT_POLLMASK` arm (:90-91) needs a pollable-by-default target, which
    `do_epoll_ctl`'s `file_can_poll` excludes for every target the contract
    has (design 9.3): modelled, unexercised. -/
def vfsPoll (fid : FileId) (pt : PollTable) : M UInt32 := do
  let file ← getFile fid
  if let some (.fixture name) := file.fOp then
    unsupported s!"vfs_poll of fixture file {name} (f_op modelled for release only)"
  if ← branch .vfsPollNoPoll (!(← fopsOf file.fOp).poll) then return DEFAULT_POLLMASK
  fopPoll fid pt file.fOp

end Leanux
