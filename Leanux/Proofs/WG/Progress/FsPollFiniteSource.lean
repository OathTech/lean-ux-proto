import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.FS.EventfdOps

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Finite poll-table allocation and the existing native poll callbacks.
All registration failures and readiness tests retain their original order. -/

def epPtableQueueProc (_file : FileId) (whead : WaitQueueRef) (_pt : PollTable) : FS.M Unit := do
  let epq := (← get).epqEpi
  if ← branch .epPtableQueueProcNoEpi epq.isNone then
    unsupported "ep_ptable_queue_proc after an earlier head's failed allocation (a second head)"
  let epiId := epq.get!
  -- pwq = kmem_cache_alloc(pwq_cache, GFP_KERNEL)
  if ← branch .epPtableQueueProcNoMem (!(← (monadLift (hiddenAllocFinite .kmemCacheAllocPwq)))) then
    modify fun k => { k with epqEpi := none }   -- epq->epi = NULL
    return
  let id := (← get).nextPwq
  -- init_waitqueue_func_entry(&pwq->wait, ep_poll_callback); pwq->whead = whead; pwq->base = epi
  setPwq id { whead := some whead, base := epiId }
  modify fun k => { k with nextPwq := id + 1 }
  let epi ← getEpi epiId
  let entry : WaitEntry := { func := .epPollCallback id }
  if ← branchCmp .epPtableQueueProcExclusive (hasFlag epi.events EPOLLEXCLUSIVE) (epi.events &&& EPOLLEXCLUSIVE).toNat 0 then
    addWaitQueueExclusive whead entry
  else addWaitQueue whead entry
  -- pwq->next = epi->pwqlist; epi->pwqlist = pwq
  setEpi epiId { epi with pwqlist := id :: epi.pwqlist }

theorem epPtableQueueProc_source (fid : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    Leanux.epPtableQueueProc fid whead pt = epPtableQueueProc fid whead pt := by
  unfold Leanux.epPtableQueueProc epPtableQueueProc
  simp only [hiddenAlloc, hiddenAlloc_finite_source] <;> rfl

def pollWait (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) : FS.M Unit := do
  if ← branch .pollWaitQproc p.qproc.isSome then
    epPtableQueueProc filp waitAddress p
    -- smp_mb()

theorem pollWait_source (fid : FileId) (whead : WaitQueueRef) (pt : PollTable) :
    Leanux.pollWait fid whead pt = pollWait fid whead pt := by
  unfold Leanux.pollWait pollWait
  simp only [epPtableQueueProc_source] <;> rfl

def pipePoll (fid : FileId) (wait : PollTable) : FS.M UInt32 := do
  let filp ← getFile fid
  let pid ← pipeOf filp
  -- WRITE_ONCE(pipe->poll_usage, true): epoll's historical semantics
  setPipe pid { (← getPipe pid) with pollUsage := true }
  -- the poll table entries first, then the racy tests (666-685)
  if ← branchCmp .pipePollReadWait (hasFlag filp.fMode FMODE_READ) (filp.fMode &&& FMODE_READ).toNat 0 then
    pollWait fid (.pipeRd pid) wait
  if ← branchCmp .pipePollWriteWait (hasFlag filp.fMode FMODE_WRITE) (filp.fMode &&& FMODE_WRITE).toNat 0 then
    pollWait fid (.pipeWr pid) wait
  -- head = READ_ONCE(pipe->head); tail = READ_ONCE(pipe->tail)
  let p ← getPipe pid
  let (head, tail) := (p.head, p.tail)
  let mut mask : UInt32 := 0
  -- the built code reuses the :672 compare of f_mode here: no operands
  if ← branch .pipePollRead (hasFlag filp.fMode FMODE_READ) then
    if ← branchCmp .pipePollNotEmpty (head != tail) head.toNat tail.toNat then
      mask := mask ||| EPOLLIN ||| EPOLLRDNORM
    -- `!pipe->writers && filp->f_pipe != pipe->w_counter`
    if ← branchCmp .pipePollNoWriters (p.writers == 0) p.writers 0 then
      if ← branchCmp .pipePollHup (filp.fPipe != p.wCounter) filp.fPipe p.wCounter then
        mask := mask ||| EPOLLHUP
  if ← branchCmp .pipePollWrite (hasFlag filp.fMode FMODE_WRITE) (filp.fMode &&& FMODE_WRITE).toNat 0 then
    if ← branchCmp .pipePollNotFull (!pipeFull head tail p.maxUsage) (pipeOccupancy head tail) p.maxUsage then
      mask := mask ||| EPOLLOUT ||| EPOLLWRNORM
    -- Linux sets EPOLLERR on pipes with no readers, like FIFOs (696-699)
    if ← branchCmp .pipePollNoReaders (p.readers == 0) p.readers 0 then
      mask := mask ||| EPOLLERR
  return mask

theorem pipePoll_source (fid : FileId) (wait : PollTable) :
    Leanux.pipePoll fid wait = pipePoll fid wait := by
  unfold Leanux.pipePoll pipePoll
  simp only [pollWait_source] <;> rfl

def eventfdPoll (fid : FileId) (wait : PollTable) : FS.M UInt32 := do
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

theorem eventfdPoll_source (fid : FileId) (wait : PollTable) :
    Leanux.eventfdPoll fid wait = eventfdPoll fid wait := by
  unfold Leanux.eventfdPoll eventfdPoll
  simp only [pollWait_source] <;> rfl

def fopPoll (fid : FileId) (pt : PollTable) : Option FopsId → FS.M UInt32
  | some .eventfd => eventfdPoll fid pt
  | some .pipefifo => pipePoll fid pt
  | some .eventpoll => unsupported "ep_eventpoll_poll through vfs_poll (select/poll on an epoll file)"
  | some (.fixture name) => unsupported s!"poll of fixture file {name}"
  | none => invariant "file->f_op is NULL"

theorem fopPoll_source (fid : FileId) (pt : PollTable) (ops : Option FopsId) :
    Leanux.fopPoll fid pt ops = fopPoll fid pt ops := by
  unfold Leanux.fopPoll fopPoll
  simp only [pipePoll_source, eventfdPoll_source] <;> rfl

def vfsPoll (fid : FileId) (pt : PollTable) : FS.M UInt32 := do
  let file ← getFile fid
  if let some (.fixture name) := file.fOp then
    unsupported s!"vfs_poll of fixture file {name} (f_op modelled for release only)"
  if ← branch .vfsPollNoPoll (!(← fopsOf file.fOp).poll) then return DEFAULT_POLLMASK
  fopPoll fid pt file.fOp

theorem vfsPoll_source (fid : FileId) (pt : PollTable) :
    Leanux.vfsPoll fid pt = vfsPoll fid pt := by
  unfold Leanux.vfsPoll vfsPoll
  simp only [fopPoll_source] <;> rfl


end Leanux.Proofs.WG.Progress.FsFinite
