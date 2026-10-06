import Leanux.FS.Kiocb
import Leanux.FS.Inode
import Leanux.Kernel.Signal
import Leanux.Kernel.Refcount

/-!
# fs/pipe.c and include/linux/pipe_fs_i.h — the pipe ring and its file operations

`pipe_read`, `pipe_write` (with `anon_pipe_buf_release`, `pipe_buf_release`,
`pipe_buf_confirm`, `pipe_update_tail`), `pipe_release`/`put_pipe_info`/
`free_pipe_info`, `alloc_pipe_info` and the buffer accounting
(`account_pipe_buffers`, `too_many_pipe_buffers_*`,
`pipe_is_unprivileged_user`), and `pipe_fcntl` (`get_pipe_info`,
`pipe_set_size`, `round_pipe_size`, `pipe_resize_ring`); `kill_fasync`
(fs/fcntl.c). Creation (`pipe2`) is in `Leanux.FS.PipeCreate`, which needs the
descriptor table. Design: docs/2026-10-05-p-pipes.md (sections 1-6,
Appendix A).

Configured-program notes: `CONFIG_WATCH_QUEUE` is unset, so
`pipe_has_watch_queue` is the constant false (pipe_fs_i.h:134-141) and its
tests (231, 448, 1319, 1341, 1392) are folded, as is the `note_loss` block of
`pipe_read`. Cut points, each stated at its call: `pipe->mutex` and the
`rd_wait` lock (one task), the wait-queue wakeups (no waiters: the domain is
single-task, so every `wake_up_*` changes no mirror state), `capable()` (the
guest runs as root: true), `get_current_user`'s and `free_uid`'s references
to `root_user` (see `getCurrentUser`), `sb_start_write_trylock` (succeeds) and
`sb_end_write`. The blocking waits (`wait_event_interruptible_exclusive`) are
`unsupported`.

The ring: `head` and `tail` are free-running `unsigned int`s, masked with
`ring_size - 1` only at dereference (`pipeBufIdx`).
-/

namespace Leanux

/-- `PIPE_MIN_DEF_BUFFERS` (fs/pipe.c:46). -/
def PIPE_MIN_DEF_BUFFERS : Nat := 2
/-- `F_SETPIPE_SZ`, `F_GETPIPE_SZ` (include/uapi/linux/fcntl.h:34-35). -/
def F_SETPIPE_SZ : Nat := 1031
def F_GETPIPE_SZ : Nat := 1032

/-- `filp->private_data` of a pipe file. -/
def pipeOf (f : File) : M PipeId :=
  match f.privateData with
  | some (.pipe id) => return id
  | some (.eventfdCtx _) => invariant "pipe operation on an eventfd file"
  | none => invariant "pipe operation on a file with NULL private_data"

/-- `pipe_full(head, tail, limit)` (pipe_fs_i.h:169-173):
    `pipe_occupancy(head, tail) >= limit`, the occupancy an unsigned
    difference. A value; the callers' tests are the decisions. -/
def pipeOccupancy (head tail : UInt32) : Nat := (head - tail).toNat
def pipeFull (head tail : UInt32) (limit : Nat) : Bool := pipeOccupancy head tail >= limit

/-- `slot & (pipe->ring_size - 1)`, bounds-checked: the C never indexes past
    `ring_size`, so an out-of-range index is a mirror invariant failure. -/
def pipeBufIdx (p : PipeInodeInfo) (slot : UInt32) : M Nat := do
  if p.ringSize == 0 || p.bufs.size != p.ringSize then
    invariant s!"pipe ring of size {p.ringSize} with {p.bufs.size} buffers"
  return (slot &&& (p.ringSize - 1).toUInt32).toNat

def getPipeBuf (pid : PipeId) (i : Nat) : M PipeBuffer := do
  match (← getPipe pid).bufs[i]? with
  | some b => return b
  | none => invariant s!"pipe->bufs[{i}] beyond ring_size"

def setPipeBuf (pid : PipeId) (i : Nat) (b : PipeBuffer) : M Unit := do
  let p ← getPipe pid
  if i < p.bufs.size then setPipe pid { p with bufs := p.bufs.set! i b }
  else invariant s!"pipe->bufs[{i}] beyond ring_size"

/-! ## Pages -/

/-- `alloc_page(GFP_HIGHUSER | __GFP_ACCOUNT)` after the environment said yes:
    a new page with `page_count == 1`. Its initial bytes are never read (only
    copied-in bytes are), so they are zero. -/
def newPipePage : M PageId := do
  let id := (← getK).nextPage
  setPage id { pageCount := 1, bytes := ByteArray.mk (Array.replicate PAGE_SIZE 0) }
  modifyK fun k => { k with nextPage := id + 1 }
  return id

/-- `put_page(page)` (include/linux/mm.h): drop one reference; the last frees
    the page. `__free_page` of a page with one reference is the same. -/
def putPipePage (id : PageId) : M Unit := do
  let pg ← getPage id
  if pg.pageCount == 0 then invariant s!"put_page on page {id} with no reference"
  if pg.pageCount == 1 then modifyK fun k => { k with pages := k.pages.erase id }
  else setPage id { pg with pageCount := pg.pageCount - 1 }

/-- `copy_page_to_iter(page, offset, bytes, to)` (lib/iov_iter.c:349-376), a
    user-memory cut point: copies `min(bytes, iov_iter_count(to))` bytes to
    the caller's buffer (appended to `World.userOut`; `cap` is the buffer's
    length) and returns the count; a fault (the environment says no) copies
    nothing. -/
def copyPageToIter (page : PageId) (offset bytes cap : Nat) : M Nat := do
  if !(← envOk .copyPageToIter) then return 0
  let out := (← get).userOut.getD ByteArray.empty
  let n := min bytes (cap - out.size)
  let pg ← getPage page
  if offset + n > pg.bytes.size then invariant s!"copy_page_to_iter beyond page {page}"
  modify fun w => { w with userOut := some (out ++ pg.bytes.extract offset (offset + n)) }
  return n

/-- `copy_page_from_iter(page, offset, bytes, from)` (lib/iov_iter.c:411-435),
    the inverse: copies `min(bytes, iov_iter_count(from))` bytes from the
    caller's buffer into the page and advances the iterator; a fault copies
    nothing. -/
def copyPageFromIter (page : PageId) (offset bytes : Nat) (src : IovIter) : M (Nat × IovIter) := do
  if !(← envOk .copyPageFromIter) then return (0, src)
  let n := min bytes src.count
  let pg ← getPage page
  if offset + n > pg.bytes.size then invariant s!"copy_page_from_iter beyond page {page}"
  setPage page { pg with bytes := src.bytes.copySlice src.pos pg.bytes offset n }
  return (n, { src with pos := src.pos + n })

/-! ## Buffer operations (`anon_pipe_buf_ops`) -/

/-- kill_fasync (fs/fcntl.c:1146-1157): `if (*fp)`; the lists are empty
    (`F_SETFL FASYNC` on a pipe is outside the stage). -/
def killFasync (hasList : Bool) : M Unit := do
  if ← branch .killFasyncList hasList then
    unsupported "kill_fasync with a fasync list (SIGIO)"

/-- anon_pipe_buf_release (fs/pipe.c:115-129): keep a page nobody else uses as
    the one-deep `tmp_page` cache, else drop the reference. -/
def anonPipeBufRelease (pid : PipeId) (buf : PipeBuffer) : M Unit := do
  let some page := buf.page | invariant "anon_pipe_buf_release of a buffer with a NULL page"
  let pg ← getPage page
  -- `page_count(page) == 1 && !pipe->tmp_page`
  let keep ← do
    if ← branchCmp .anonBufReleaseSole (pg.pageCount == 1) pg.pageCount 1 then
      branch .anonBufReleaseNoTmp (← getPipe pid).tmpPage.isNone
    else pure false
  if keep then setPipe pid { (← getPipe pid) with tmpPage := some page }
  else putPipePage page

/-- pipe_buf_release (pipe_fs_i.h:211-220): `buf->ops = NULL`, then
    `ops->release`, which is `anon_pipe_buf_release` (the only ops). -/
def pipeBufRelease (pid : PipeId) (i : Nat) : M Unit := do
  let buf ← getPipeBuf pid i
  if !buf.ops then invariant "pipe_buf_release of a buffer with NULL ops"
  setPipeBuf pid i { buf with ops := false }
  anonPipeBufRelease pid buf

/-- pipe_buf_confirm (pipe_fs_i.h:227-233): `anon_pipe_buf_ops` has no
    `confirm`. -/
def pipeBufConfirm (buf : PipeBuffer) : M Int := do
  if !buf.ops then invariant "pipe_buf_confirm of a buffer with NULL ops"
  if ← branch .pipeBufConfirmNoConfirm true then return 0
  unsupported "pipe_buf_confirm: ops->confirm"

/-- pipe_update_tail (fs/pipe.c:220-247): release the buffer at slot `i` and
    advance `pipe->tail` to `tail + 1`. -/
def pipeUpdateTail (pid : PipeId) (i : Nat) (tail : UInt32) : M UInt32 := do
  pipeBufRelease pid i
  -- pipe_has_watch_queue(pipe) is the constant false (231)
  setPipe pid { (← getPipe pid) with tail := tail + 1 }
  return tail + 1

/-! ## Accounting -/

/-- account_pipe_buffers (fs/pipe.c:765-769):
    `atomic_long_add_return(new - old, &user->pipe_bufs)`. -/
def accountPipeBuffers (old new : Nat) : M Nat := do
  let v : Int := (← getK).user.pipeBufs + new - old
  if v < 0 then invariant "user->pipe_bufs below zero"
  modifyK fun k => { k with user := { k.user with pipeBufs := v.toNat } }
  return v.toNat

/-- too_many_pipe_buffers_soft (fs/pipe.c:771-776). -/
def tooManyPipeBuffersSoft (userBufs : Nat) : M Bool := do
  let soft := (← getK).pipeUserPagesSoft
  if ← branchCmp .tooManySoftLimit (soft != 0) soft 0 then
    branchCmp .tooManySoftOver (userBufs > soft) userBufs soft
  else return false

/-- too_many_pipe_buffers_hard (fs/pipe.c:778-783). -/
def tooManyPipeBuffersHard (userBufs : Nat) : M Bool := do
  let hard := (← getK).pipeUserPagesHard
  if ← branchCmp .tooManyHardLimit (hard != 0) hard 0 then
    branchCmp .tooManyHardOver (userBufs > hard) userBufs hard
  else return false

/-- pipe_is_unprivileged_user (fs/pipe.c:785-788). `capable()` is a cut point:
    the guest runs as root, so both are true (design section 5). -/
def pipeIsUnprivilegedUser : M Bool := do
  let capable := true
  if ← branch .unprivNoResource !capable then
    branch .unprivNoAdmin !capable
  else return false

/-- `root_user.__count` before `get_current_user`'s `refcount_inc`.

    OPEN ISSUE (P2 report): `get_current_user()` → `get_uid()` →
    `refcount_inc(&root_user.__count)` is inlined into `alloc_pipe_info`
    (fs/pipe.c:794), so `__refcount_add`'s decisions at refcount.h:189-191
    are witnessed there and must be reported. Their A3 operand is the
    guest-wide reference count of `root_user` (every root credential, kernel
    threads included), which the mirror does not model and which changes as
    processes come and go. The mirror reports the outcomes the contract fixes
    (a live `root_user`: not zero, no overflow) with this placeholder as the
    operand, so A3 rejects `__refcount_add.old_zero` at that site, noisily,
    until the treatment is decided (the design's "refcount cut" does not
    hold for an inlined helper with anchored decisions). -/
def ROOT_USER_COUNT_PLACEHOLDER : Nat := 2

/-- get_current_user (include/linux/cred.h) → get_uid
    (include/linux/sched/user.h:49-53): `refcount_inc(&u->__count)` on
    `root_user`. -/
def getCurrentUser : M UserId := do
  refcountInc ROOT_USER_COUNT_PLACEHOLDER
  return .root

/-! ## Allocation and release -/

/-- alloc_pipe_info (fs/pipe.c:790-837). `get_current_user`/`free_uid`: see
    `getCurrentUser`. -/
def allocPipeInfo : M (Option PipeId) := do
  let mut pipeBufs := PIPE_DEF_BUFFERS
  let user ← getCurrentUser
  let maxSize := (← getK).pipeMaxSize
  -- pipe = kzalloc(sizeof(struct pipe_inode_info), GFP_KERNEL_ACCOUNT)
  if ← branch .allocPipeInfoNoMem !(← envOk .kzallocPipeInfo) then
    return none  -- out_free_uid: free_uid(user)
  -- `pipe_bufs * PAGE_SIZE > max_size && !capable(CAP_SYS_RESOURCE)`
  if ← branchCmp .allocPipeInfoOverMax (PIPE_DEF_BUFFERS * PAGE_SIZE > maxSize) maxSize (PIPE_DEF_BUFFERS * PAGE_SIZE) then
    if ← branch .allocPipeInfoNotCapable false then  -- capable(): root
      pipeBufs := maxSize >>> 12
  let mut userBufs ← accountPipeBuffers 0 pipeBufs
  if ← branch .allocPipeInfoSoft (← tooManyPipeBuffersSoft userBufs) then
    if ← branch .allocPipeInfoSoftUnpriv (← pipeIsUnprivilegedUser) then
      userBufs ← accountPipeBuffers pipeBufs PIPE_MIN_DEF_BUFFERS
      pipeBufs := PIPE_MIN_DEF_BUFFERS
  let revert ← do
    if ← branch .allocPipeInfoHard (← tooManyPipeBuffersHard userBufs) then
      branch .allocPipeInfoHardUnpriv (← pipeIsUnprivilegedUser)
    else pure false
  if !revert then
    -- pipe->bufs = kcalloc(pipe_bufs, sizeof(struct pipe_buffer), GFP_KERNEL_ACCOUNT)
    if ← branch .allocPipeInfoBufs (← envOk .kcallocPipeBufs) then
      -- init_waitqueue_head (x2), r_counter = w_counter = 1, max_usage =
      -- ring_size = nr_accounted = pipe_bufs, user, mutex_init
      let pid := (← getK).nextPipe
      setPipe pid { maxUsage := pipeBufs, ringSize := pipeBufs, nrAccounted := pipeBufs,
                    rCounter := 1, wCounter := 1, bufs := Array.replicate pipeBufs {}, user }
      modifyK fun k => { k with nextPipe := pid + 1 }
      return some pid
  -- out_revert_acct:
  _ ← accountPipeBuffers pipeBufs 0
  -- kfree(pipe); out_free_uid: free_uid(user)
  return none

/-- free_pipe_info (fs/pipe.c:839-863). `free_uid` is a cut (see
    `getCurrentUser`). -/
def freePipeInfo (pid : PipeId) : M Unit := do
  _ ← accountPipeBuffers (← getPipe pid).nrAccounted 0
  -- free_uid(pipe->user)
  let mut i := 0
  repeat
    let p ← getPipe pid
    if !(← branch .freePipeInfoLoop (i < p.ringSize)) then break
    if ← branch .freePipeInfoBufOps (← getPipeBuf pid i).ops then
      pipeBufRelease pid i
    i := i + 1
  if let some page := (← getPipe pid).tmpPage then
    _ ← branch .freePipeInfoTmpPage true
    putPipePage page  -- __free_page(pipe->tmp_page)
  else
    _ ← branch .freePipeInfoTmpPage false
  -- kfree(pipe->bufs); kfree(pipe)
  modifyK fun k => { k with pipes := k.pipes.erase pid }

/-- put_pipe_info (fs/pipe.c:707-720), under `inode->i_lock`. -/
def putPipeInfo (ino : PipefsInodeId) (pid : PipeId) : M Unit := do
  let p ← getPipe pid
  if p.files == 0 then invariant "put_pipe_info with pipe->files == 0"
  let files := p.files - 1
  setPipe pid { p with files }
  let kill ← do
    if ← branchCmp .putPipeInfoLast (files == 0) files 0 then
      setInode ino { (← getInode ino) with iPipe := none }
      pure true
    else pure false
  if ← branch .putPipeInfoKill kill then freePipeInfo pid

/-- pipe_release (fs/pipe.c:722-744), the `release` operation:
    `f_op->release(inode, file)` from `__fput`. -/
def pipeRelease (ino : PipefsInodeId) (fid : FileId) : M Int := do
  let f ← getFile fid
  let pid ← pipeOf f
  -- mutex_lock(&pipe->mutex)
  if ← branchCmp .pipeReleaseRead (hasFlag f.fMode FMODE_READ) (f.fMode &&& FMODE_READ).toNat 0 then
    let p ← getPipe pid
    if p.readers == 0 then invariant "pipe_release: readers below zero"
    setPipe pid { p with readers := p.readers - 1 }
  if ← branchCmp .pipeReleaseWrite (hasFlag f.fMode FMODE_WRITE) (f.fMode &&& FMODE_WRITE).toNat 0 then
    let p ← getPipe pid
    if p.writers == 0 then invariant "pipe_release: writers below zero"
    setPipe pid { p with writers := p.writers - 1 }
  let p ← getPipe pid
  -- `!pipe->readers != !pipe->writers`
  if ← branch .pipeReleaseOneSide ((p.readers == 0) != (p.writers == 0)) then
    -- wake_up_interruptible_all(&pipe->rd_wait), (&pipe->wr_wait): no waiters
    killFasync p.fasyncReaders
    killFasync p.fasyncWriters
  -- mutex_unlock(&pipe->mutex)
  putPipeInfo ino pid
  return 0

/-! ## read and write -/

/-- pipe_read (fs/pipe.c:249-409), the `read_iter` operation. `count` is
    `iov_iter_count(to)`; the bytes go to `World.userOut`. -/
def pipeRead (iocb : Kiocb) (count : Nat) : M Int := do
  let mut totalLen := count
  let filp ← getFile iocb.filp
  let pid ← pipeOf filp
  -- Null read succeeds.
  if ← branchCmp .pipeReadNull (totalLen == 0) totalLen 0 then return 0
  let mut ret : Int := 0
  modify fun w => { w with userOut := some ByteArray.empty }
  -- mutex_lock(&pipe->mutex)
  let p0 ← getPipe pid
  let wasFull := pipeFull p0.head p0.tail p0.maxUsage
  let mut wakeNextReader := false
  repeat
    -- head = smp_load_acquire(&pipe->head); the note_loss block is compiled out
    let p ← getPipe pid
    let head := p.head
    let mut tail := p.tail
    if ← branchCmp .pipeReadNotEmpty (head != tail) head.toNat tail.toNat then
      let i ← pipeBufIdx p tail
      let buf ← getPipeBuf pid i
      let mut chars := buf.len
      if ← branchCmp .pipeReadCharsOver (chars > totalLen) chars totalLen then
        if ← branchCmp .pipeReadWhole (hasFlag buf.flags PIPE_BUF_FLAG_WHOLE)
            (buf.flags &&& PIPE_BUF_FLAG_WHOLE).toNat 0 then
          unsupported "pipe_read: PIPE_BUF_FLAG_WHOLE (a notification buffer)"
        chars := totalLen
      let error ← pipeBufConfirm buf
      if ← branch .pipeReadConfirmError (error != 0) then
        unsupported "pipe_read: pipe_buf_confirm failed"
      let some page := buf.page | invariant "pipe_read: a buffer with a NULL page"
      let written ← copyPageToIter page buf.offset chars count
      if ← branchCmp .pipeReadShortCopy (written < chars) written chars then
        if ← branchCmp .pipeReadFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
        break
      ret := ret + chars
      let mut buf := { buf with offset := buf.offset + chars, len := buf.len - chars }
      -- Was it a packet buffer? Clean up and exit
      if ← branchCmp .pipeReadPacket (hasFlag buf.flags PIPE_BUF_FLAG_PACKET)
          (buf.flags &&& PIPE_BUF_FLAG_PACKET).toNat 0 then
        totalLen := chars
        buf := { buf with len := 0 }
      setPipeBuf pid i buf
      if ← branch .pipeReadBufEmpty (buf.len == 0) then
        tail ← pipeUpdateTail pid i tail
      totalLen := totalLen - chars
      if ← branch .pipeReadDone (totalLen == 0) then break  -- common path
      if ← branchCmp .pipeReadMore (head != tail) head.toNat tail.toNat then continue
    let p ← getPipe pid
    if ← branchCmp .pipeReadNoWriters (p.writers == 0) p.writers 0 then break
    if ← branchCmp .pipeReadHaveData (ret != 0) ret 0 then break
    -- `(filp->f_flags & O_NONBLOCK) || (iocb->ki_flags & IOCB_NOWAIT)`
    let nonblock ← do
      if ← branchCmp .pipeReadNonblock (hasFlag filp.fFlags O_NONBLOCK) (filp.fFlags &&& O_NONBLOCK).toNat 0 then
        pure true
      else branchCmp .pipeReadNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
    if nonblock then
      ret := -EAGAIN
      break
    unsupported "pipe_read: blocking wait (wait_event_interruptible_exclusive)"
  let p ← getPipe pid
  if ← branchCmp .pipeReadEmptyAtEnd (p.head == p.tail) p.head.toNat p.tail.toNat then
    wakeNextReader := false
  -- mutex_unlock(&pipe->mutex)
  if ← branch .pipeReadWasFull wasFull then
    pure ()  -- wake_up_interruptible_sync_poll(&pipe->wr_wait, ...): no waiters
  if ← branch .pipeReadWakeNextReader wakeNextReader then
    pure ()  -- wake_up_interruptible_sync_poll(&pipe->rd_wait, ...): no waiters
  killFasync p.fasyncWriters
  if ← branchCmp .pipeReadPositive (ret > 0) ret 0 then
    fileAccessed (← getFile iocb.filp)
  return ret

/-- pipe_write (fs/pipe.c:452-583) from the null-write test to `out:`. Every
    `goto out` is a `return`; the result is `ret` and `was_empty`. -/
def pipeWriteToOut (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) : M (Int × Bool) := do
  let totalLen := src.count
  let mut src := src
  -- mutex_lock(&pipe->mutex)
  let p ← getPipe pid
  if ← branchCmp .pipeWriteNoReaders (p.readers == 0) p.readers 0 then
    _ ← sendSig SIGPIPE 0
    return (-EPIPE, false)
  -- If it wasn't empty we try to merge new data into the last buffer.
  let head := p.head
  let wasEmpty := head == p.tail
  let chars := totalLen % PAGE_SIZE  -- total_len & (PAGE_SIZE-1)
  let mut ret : Int := 0
  let merge ← do
    if ← branchCmp .pipeWriteChars (chars != 0) chars 0 then branch .pipeWriteNotWasEmpty !wasEmpty
    else pure false
  if merge then
    let i ← pipeBufIdx p (head - 1)
    let buf ← getPipeBuf pid i
    let offset := buf.offset + buf.len
    let fits ← do
      if ← branchCmp .pipeWriteCanMerge (hasFlag buf.flags PIPE_BUF_FLAG_CAN_MERGE)
          (buf.flags &&& PIPE_BUF_FLAG_CAN_MERGE).toNat 0 then
        branchCmp .pipeWriteFits (offset + chars <= PAGE_SIZE) (offset + chars) PAGE_SIZE
      else pure false
    if fits then
      ret ← pipeBufConfirm buf
      if ← branch .pipeWriteMergeConfirmErr (ret != 0) then return (ret, wasEmpty)
      let some page := buf.page | invariant "pipe_write: a buffer with a NULL page"
      let (n, src') ← copyPageFromIter page offset chars src
      src := src'
      ret := n
      if ← branchCmp .pipeWriteMergeShort (ret < chars) ret chars then return (-EFAULT, wasEmpty)
      setPipeBuf pid i { (← getPipeBuf pid i) with len := buf.len + n }
      if ← branchCmp .pipeWriteMergeDone (src.count == 0) src.count 0 then return (ret, wasEmpty)
  repeat
    let p ← getPipe pid
    if ← branch .pipeWriteLoopNoReaders (p.readers == 0) then
      _ ← sendSig SIGPIPE 0
      if ← branchCmp .pipeWriteLoopNoRet (ret == 0) ret 0 then ret := -EPIPE
      break
    let head := p.head
    if ← branchCmp .pipeWriteNotFull (!pipeFull head p.tail p.maxUsage) (pipeOccupancy head p.tail) p.maxUsage then
      let mut page := p.tmpPage
      if ← branch .pipeWriteNoTmpPage page.isNone then
        -- alloc_page(GFP_HIGHUSER | __GFP_ACCOUNT)
        if ← branch .pipeWriteAllocFailed !(← envOk .allocPipePage) then
          -- `ret = ret ? : -ENOMEM`
          if !(← branchCmp .pipeWriteAllocRet (ret != 0) ret 0) then ret := -ENOMEM
          break
        let pg ← newPipePage
        page := some pg
        setPipe pid { (← getPipe pid) with tmpPage := some pg }
      let some pg := page | invariant "unreachable"
      -- Allocate a slot in the ring in advance and attach an empty buffer.
      setPipe pid { (← getPipe pid) with head := head + 1 }
      let i ← pipeBufIdx (← getPipe pid) head
      -- `is_packetized(filp)` (411-414): `(file->f_flags & O_DIRECT) != 0`
      let flags := if ← branchCmp .pipeWritePacketized (hasFlag filp.fFlags O_DIRECT)
          (filp.fFlags &&& O_DIRECT).toNat 0 then PIPE_BUF_FLAG_PACKET else PIPE_BUF_FLAG_CAN_MERGE
      setPipeBuf pid i { page := some pg, ops := true, offset := 0, len := 0, flags }
      setPipe pid { (← getPipe pid) with tmpPage := none }
      let (copied, src') ← copyPageFromIter pg 0 PAGE_SIZE src
      src := src'
      -- `unlikely(copied < PAGE_SIZE && iov_iter_count(from))`
      let fault ← do
        if ← branchCmp .pipeWriteShortCopy (copied < PAGE_SIZE) copied PAGE_SIZE then
          branchCmp .pipeWriteShortCopyLeft (src.count != 0) src.count 0
        else pure false
      if fault then
        if ← branchCmp .pipeWriteFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
        break
      ret := ret + copied
      setPipeBuf pid i { (← getPipeBuf pid i) with len := copied }
      if ← branchCmp .pipeWriteDone (src.count == 0) src.count 0 then break
    -- the local `head` (505): one behind `pipe->head` after an insertion (526)
    let p ← getPipe pid
    if ← branch .pipeWriteStaleNotFull (!pipeFull head p.tail p.maxUsage) then
      continue
    -- Wait for buffer space to become available.
    let nonblock ← do
      if ← branchCmp .pipeWriteNonblock (hasFlag filp.fFlags O_NONBLOCK) (filp.fFlags &&& O_NONBLOCK).toNat 0 then
        pure true
      else branchCmp .pipeWriteNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
    if nonblock then
      if ← branchCmp .pipeWriteNoRet (ret == 0) ret 0 then ret := -EAGAIN
      break
    unsupported "pipe_write: blocking wait (signal_pending, wait_event_interruptible_exclusive)"
  return (ret, wasEmpty)

/-- pipe_write (fs/pipe.c:426-613), the `write_iter` operation; `src` is the
    caller's buffer (`from`). -/
def pipeWrite (iocb : Kiocb) (src : IovIter) : M Int := do
  let filp ← getFile iocb.filp
  let pid ← pipeOf filp
  -- pipe_has_watch_queue(pipe) is the constant false (448)
  -- Null write succeeds.
  if ← branchCmp .pipeWriteNull (src.count == 0) src.count 0 then return 0
  let (ret, wasEmpty) ← pipeWriteToOut iocb filp pid src
  let mut ret := ret
  -- out:
  let mut wakeNextWriter := false
  let p ← getPipe pid
  if ← branchCmp .pipeWriteFullAtOut (pipeFull p.head p.tail p.maxUsage) (pipeOccupancy p.head p.tail) p.maxUsage then
    wakeNextWriter := false
  -- mutex_unlock(&pipe->mutex)
  let wake ← do
    if ← branch .pipeWriteWasEmpty wasEmpty then pure true
    else branch .pipeWritePollUsage p.pollUsage
  if wake then pure ()  -- wake_up_interruptible_sync_poll(&pipe->rd_wait, ...): no waiters
  killFasync p.fasyncReaders
  if ← branch .pipeWriteWakeNextWriter wakeNextWriter then
    pure ()  -- wake_up_interruptible_sync_poll(&pipe->wr_wait, ...): no waiters
  -- `ret > 0 && sb_start_write_trylock(file_inode(filp)->i_sb)`: the trylock is a
  -- cut that succeeds (design section 5)
  let update ← do
    if ← branchCmp .pipeWritePositive (ret > 0) ret 0 then branch .pipeWriteSbTrylock true
    else pure false
  if update then
    let err ← fileUpdateTime (← getFile iocb.filp)
    if ← branchCmp .pipeWriteUpdateTimeErr (err != 0) err 0 then ret := err
    -- sb_end_write(file_inode(filp)->i_sb): a cut
  return ret

/-! ## F_SETPIPE_SZ and F_GETPIPE_SZ -/

/-- `roundup_pow_of_two(n)` (include/linux/log2.h) for `1 ≤ n ≤ 2^31`. -/
def roundupPowOfTwoUL (n : Nat) : Nat := Id.run do
  let mut p := 1
  while p < n do p := 2 * p
  return p

/-- round_pipe_size (fs/pipe.c:1247-1257); `size` is an `unsigned int`. -/
def roundPipeSize (size : Nat) : M Nat := do
  if ← branchCmp .roundPipeSizeTooBig (size > 2 ^ 31) size (2 ^ 31) then return 0
  -- Minimum pipe size, as required by POSIX
  if ← branchCmp .roundPipeSizeSmall (size < PAGE_SIZE) size PAGE_SIZE then return PAGE_SIZE
  return roundupPowOfTwoUL size

/-- Copy `len` buffers from `src[srcOff..]` to `dst[dstOff..]` (a `memcpy` of
    `struct pipe_buffer`s), bounds-checked. -/
def copyPipeBufs (dst src : Array PipeBuffer) (dstOff srcOff len : Nat) : M (Array PipeBuffer) := do
  if dstOff + len > dst.size || srcOff + len > src.size then
    invariant "pipe_resize_ring: memcpy beyond a ring"
  return (List.range len).foldl (fun a k => a.set! (dstOff + k) src[srcOff + k]!) dst

/-- pipe_resize_ring (fs/pipe.c:1266-1329). -/
def pipeResizeRing (pid : PipeId) (nrSlots : Nat) : M Int := do
  -- bufs = kcalloc(nr_slots, sizeof(*bufs), GFP_KERNEL_ACCOUNT | __GFP_NOWARN)
  if ← branch .resizeRingNoMem !(← envOk .kcallocResizeBufs) then return -ENOMEM
  -- spin_lock_irq(&pipe->rd_wait.lock)
  let p ← getPipe pid
  let mask := p.ringSize - 1
  let n := pipeOccupancy p.head p.tail
  if ← branchCmp .resizeRingBusy (nrSlots < n) nrSlots n then
    return -EBUSY  -- spin_unlock_irq; kfree(bufs)
  let mut bufs : Array PipeBuffer := Array.replicate nrSlots {}
  -- The pipe array wraps around, so just start the new one at zero.
  if ← branchCmp .resizeRingNonEmpty (n > 0) n 0 then
    let h := (p.head &&& mask.toUInt32).toNat
    let t := (p.tail &&& mask.toUInt32).toNat
    if ← branchCmp .resizeRingNoWrap (h > t) h t then
      bufs ← copyPipeBufs bufs p.bufs 0 t n
    else
      let tsize := p.ringSize - t
      if ← branchCmp .resizeRingHeadPart (h > 0) h 0 then
        bufs ← copyPipeBufs bufs p.bufs tsize 0 h
      bufs ← copyPipeBufs bufs p.bufs 0 t tsize
  -- kfree(pipe->bufs); pipe->bufs = bufs; pipe->ring_size = nr_slots
  let mut maxUsage := p.maxUsage
  if ← branch .resizeRingShrinkMaxUsage (maxUsage > nrSlots) then maxUsage := nrSlots
  -- tail = 0, head = n; `!pipe_has_watch_queue(pipe)` is the constant true (1319):
  -- max_usage = nr_accounted = nr_slots
  setPipe pid { p with bufs, ringSize := nrSlots, maxUsage, tail := 0, head := n.toUInt32 }
  setPipe pid { (← getPipe pid) with maxUsage := nrSlots, nrAccounted := nrSlots }
  -- spin_unlock_irq; wake_up_interruptible(&pipe->wr_wait): no waiters
  return 0

/-- pipe_set_size (fs/pipe.c:1335-1380), with `pipe->mutex` held. -/
def pipeSetSize (pid : PipeId) (arg : Nat) : M Int := do
  -- pipe_has_watch_queue(pipe) is the constant false (1341)
  let size ← roundPipeSize arg
  let nrSlots := size >>> 12  -- size >> PAGE_SHIFT
  if ← branchCmp .pipeSetSizeZero (nrSlots == 0) nrSlots 0 then return -EINVAL
  -- `nr_slots > pipe->max_usage && size > pipe_max_size && !capable(CAP_SYS_RESOURCE)`
  let p ← getPipe pid
  let maxSize := (← getK).pipeMaxSize
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
  let ret ← do
    if limited then pure (-EPERM)
    else
      let ret ← pipeResizeRing pid nrSlots
      if ← branchCmp .pipeSetSizeResizeErr (ret < 0) ret 0 then pure ret
      else return ((← getPipe pid).maxUsage * PAGE_SIZE : Nat)
  -- out_revert_acct:
  _ ← accountPipeBuffers nrSlots (← getPipe pid).nrAccounted
  return ret

/-- get_pipe_info (fs/pipe.c:1386-1395) with `for_splice` false (its test
    folds away with `pipe_has_watch_queue`). -/
def getPipeInfo (f : File) : M (Option PipeId) := do
  -- `file->f_op != &pipefifo_fops || !pipe`, pipe = file->private_data
  if ← branch .getPipeInfoNotPipe (f.fOp != some .pipefifo) then return none
  let pipe? ← match f.privateData with
    | some (.pipe id) => pure (some id)
    | none => pure none
    | some (.eventfdCtx _) => invariant "a pipefifo file whose private_data is an eventfd context"
  if ← branch .getPipeInfoNoPipe pipe?.isNone then return none
  return pipe?

/-- pipe_fcntl (fs/pipe.c:1397-1422). `cmd` is the command number: do_fcntl
    routes only F_SETPIPE_SZ and F_GETPIPE_SZ here. -/
def pipeFcntl (fid : FileId) (cmd : Nat) (arg : Nat) : M Int := do
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

end Leanux
