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

/-- `poll_wait(filp, wait_address, p)` (poll.h:42-46). `p` and `wait_address`
    are never NULL on the modelled paths (`ep_item_poll` always passes its
    table, every caller names an embedded head), so the mirror holds them as
    values and the live test of `p && p->_qproc && wait_address` is
    `p->_qproc`. The registration it calls is `ep_ptable_queue_proc`
    (fs/eventpoll.c:1545-1566), the epoll mirror's (stream S). -/
def pollWait (filp : FileId) (waitAddress : WaitQueueRef) (p : PollTable) : M Unit := do
  if ← branch .pollWaitQproc p.qproc.isSome then
    unsupported s!"ep_ptable_queue_proc (fs/eventpoll.c:1545-1566) for file {filp} on {repr waitAddress}: the epoll mirror, stream S"
    -- smp_mb()

end Leanux
