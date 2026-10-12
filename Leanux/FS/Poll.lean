import Leanux.FS.Wait

/-!
# include/linux/poll.h — the poll table

`poll_table` (poll.h:37-40), `poll_wait` (poll.h:42-46) and `DEFAULT_POLLMASK`
(poll.h:24). Design: docs/2026-10-12-epoll-design.md, 4.2. The `f_op->poll`
implementations sit with their files (`pipePoll` in `Leanux.FS.Pipe`,
`eventfdPoll` in `Leanux.FS.EventfdOps`), and `vfs_poll` (poll.h:88-93) with
the other `f_op` dispatchers in `Leanux.FS.EventfdOps`, after every
implementation it dispatches to.
-/

namespace Leanux

/-- `DEFAULT_POLLMASK` (poll.h:24). -/
def DEFAULT_POLLMASK : UInt32 := EPOLLIN ||| EPOLLOUT ||| EPOLLRDNORM ||| EPOLLWRNORM

/-- `struct poll_table_struct` (poll.h:37-40). `_qproc` is a function pointer
    with one non-NULL value in the domain, `ep_ptable_queue_proc` with the
    `ep_pqueue`'s `epi` (fs/eventpoll.c:1545-1566); `_key` is the requested
    events, `~(__poll_t)0` from `init_poll_funcptr` (poll.h:77-81). -/
structure PollTable where
  qproc : Option EpiId := none
  key : UInt32 := 0xffffffff
  deriving Repr, BEq

/-- `ep_ptable_queue_proc(file, whead, pt)` (fs/eventpoll.c:1540-1565,
    `epq = container_of(pt, struct ep_pqueue, pt)`, whose
    `epi` is `Kernel.epqEpi`; an `eppoll_entry` with `ep_poll_callback` joins
    `whead`, exclusive at the tail for `EPOLLEXCLUSIVE`, else at the head,
    and the head of `epi->pwqlist`. It lives here, with `poll_wait`, because
    `poll_wait` calls it (stream S). -/
def epPtableQueueProc (_file : FileId) (whead : WaitQueueRef) (_pt : PollTable) : M Unit := do
  let epq := (← getK).epqEpi
  if ← branch .epPtableQueueProcNoEpi epq.isNone then
    unsupported "ep_ptable_queue_proc after an earlier head's failed allocation (a second head)"
  let epiId := epq.get!
  -- pwq = kmem_cache_alloc(pwq_cache, GFP_KERNEL)
  if ← branch .epPtableQueueProcNoMem (!(← hiddenAlloc .kmemCacheAllocPwq)) then
    modifyK fun k => { k with epqEpi := none }   -- epq->epi = NULL
    return
  let id := (← getK).nextPwq
  -- init_waitqueue_func_entry(&pwq->wait, ep_poll_callback); pwq->whead = whead; pwq->base = epi
  setPwq id { whead := some whead, base := epiId }
  modifyK fun k => { k with nextPwq := id + 1 }
  let epi ← getEpi epiId
  let entry : WaitEntry := { func := .epPollCallback id }
  if ← branchCmp .epPtableQueueProcExclusive (hasFlag epi.events EPOLLEXCLUSIVE) (epi.events &&& EPOLLEXCLUSIVE).toNat 0 then
    addWaitQueueExclusive whead entry
  else addWaitQueue whead entry
  -- pwq->next = epi->pwqlist; epi->pwqlist = pwq
  setEpi epiId { epi with pwqlist := id :: epi.pwqlist }

/-- `poll_wait(filp, wait_address, p)` (poll.h:42-46). `p` and `wait_address`
    are never NULL on the modelled paths (`ep_item_poll` always passes its
    table, every caller names an embedded head), so the mirror holds them as
    values and the live test of `p && p->_qproc && wait_address` is
    `p->_qproc`. The registration it calls is `ep_ptable_queue_proc`. -/
def pollWait (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) : M Unit := do
  if ← branch .pollWaitQproc p.qproc.isSome then
    epPtableQueueProc filp waitAddress p
    -- smp_mb()

end Leanux
