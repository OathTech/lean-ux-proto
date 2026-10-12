import Leanux.Kernel.Defs

/-!
# kernel/sched/wait.c and include/linux/wait.h — the wait-queue service

The queue operations (`add_wait_queue`, `add_wait_queue_exclusive`,
`remove_wait_queue`, `waitqueue_active`), the wake walk (`__wake_up_common`)
and the wrappers the slice's wake sites use (`__wake_up`,
`__wake_up_locked_key`, `__wake_up_sync_key` and the `wake_up_*` macros of
wait.h:219-246). Design: docs/2026-10-12-epoll-design.md, sections 2.5 and
4.2. The event masks a wake carries as its key are the uapi ones
(include/uapi/linux/eventpoll.h), kept here with the task states they pair
with.

Each head lives in the object that embeds it (`WaitQueueRef`); the head's
spinlock and `lockdep_assert_held` are cuts (one task). The walk
(wait.c:73-97) calls each entry's `func` through `WaitEntry.call`. In tier 1
the only callback is `ep_poll_callback` (fs/eventpoll.c:1429-1525), which
belongs to the epoll mirror (stream S): until it lands, `WaitEntry.call`
stops on it. That callback re-enters the walk on another head
(`ep_poll_safewake`, nested epoll), so when it lands it joins `wakeUpCommon`
in one mutual group. The C walks the live list; no callback in the domain
edits the queue being walked (`POLLFREE` is out of scope, `ep_poll_safewake`
walks a different head), so the mirror walks a snapshot and checks afterwards
that the queue is unchanged (`invariant`), keeping the C's shape visible at
this boundary rather than relying on it silently.

Witnesses: `kernel/sched/Makefile` sets `KCOV_INSTRUMENT := n`, so no line of
wait.c owns a KCOV point and no decision here could be witnessed. The walk's
tests (:82, :90, :92) and the wrappers' (:169) are therefore plain mirror
control flow, not `branch` decisions: they are observed through the callbacks
they run, whose decisions are in the instrumented fs/eventpoll.c.
`waitqueue_active` (wait.h:125-127) is inlined into its callers and its tests
are decisions there (`eventfd_read.waitqueue_active`,
`eventfd_write.waitqueue_active`).
-/

namespace Leanux

/-! ## Event masks (include/uapi/linux/eventpoll.h:31-69), `__poll_t` -/

def EPOLLIN : UInt32 := 0x00000001
def EPOLLPRI : UInt32 := 0x00000002
def EPOLLOUT : UInt32 := 0x00000004
def EPOLLERR : UInt32 := 0x00000008
def EPOLLHUP : UInt32 := 0x00000010
def EPOLLNVAL : UInt32 := 0x00000020
def EPOLLRDNORM : UInt32 := 0x00000040
def EPOLLRDBAND : UInt32 := 0x00000080
def EPOLLWRNORM : UInt32 := 0x00000100
def EPOLLWRBAND : UInt32 := 0x00000200
def EPOLLMSG : UInt32 := 0x00000400
def EPOLLRDHUP : UInt32 := 0x00002000
def EPOLLEXCLUSIVE : UInt32 := (1 : UInt32) <<< 28
def EPOLLWAKEUP : UInt32 := (1 : UInt32) <<< 29
def EPOLLONESHOT : UInt32 := (1 : UInt32) <<< 30
def EPOLLET : UInt32 := (1 : UInt32) <<< 31

/-- Task states a wake selects (include/linux/sched.h:100-100, 136). -/
def TASK_INTERRUPTIBLE : UInt32 := 0x1
def TASK_UNINTERRUPTIBLE : UInt32 := 0x2
def TASK_NORMAL : UInt32 := TASK_INTERRUPTIBLE ||| TASK_UNINTERRUPTIBLE
/-- `WF_SYNC` (kernel/sched/sched.h:2307): the waker is about to sleep. -/
def WF_SYNC : UInt32 := 0x10

/-! ## The heads -/

/-- The queue a `wait_queue_head_t *` names. -/
def getWaitQueue : WaitQueueRef → M WaitQueue
  | .pipeRd p => return (← getPipe p).rdWait
  | .pipeWr p => return (← getPipe p).wrWait
  | .eventfdWqh c => return (← getCtx c).wqh
  | .epWq e => return (← getEp e).wq
  | .epPollWait e => return (← getEp e).pollWait

def setWaitQueue (r : WaitQueueRef) (q : WaitQueue) : M Unit := do
  match r with
  | .pipeRd p => setPipe p { (← getPipe p) with rdWait := q }
  | .pipeWr p => setPipe p { (← getPipe p) with wrWait := q }
  | .eventfdWqh c => setCtx c { (← getCtx c) with wqh := q }
  | .epWq e => setEp e { (← getEp e) with wq := q }
  | .epPollWait e => setEp e { (← getEp e) with pollWait := q }

/-- `waitqueue_active` (wait.h:125-127): `!list_empty(&wq_head->head)`. A
    value; the caller's test is the decision. -/
def waitqueueActive (r : WaitQueueRef) : M Bool :=
  return !(← getWaitQueue r).entries.isEmpty

/-! ## Queueing (wait.c:17-57) -/

/-- `add_wait_queue` (wait.c:17-25): clears `WQ_FLAG_EXCLUSIVE`, then
    `__add_wait_queue` (wait.h:169-179) inserts after the `WQ_FLAG_PRIORITY`
    entries, at the head: no entry in the domain carries that flag
    (`add_wait_queue_priority` has no caller here), so its loop stops at the
    first entry or does not run, and the insertion point is the head. -/
def addWaitQueue (r : WaitQueueRef) (e : WaitEntry) : M Unit := do
  let q ← getWaitQueue r
  -- spin_lock_irqsave(&wq_head->lock, flags): a cut
  setWaitQueue r { q with entries := { e with exclusive := false } :: q.entries }
  -- spin_unlock_irqrestore

/-- `add_wait_queue_exclusive` (wait.c:28-36): sets `WQ_FLAG_EXCLUSIVE`, then
    `__add_wait_queue_entry_tail` (wait.h:193-195) appends at the tail. -/
def addWaitQueueExclusive (r : WaitQueueRef) (e : WaitEntry) : M Unit := do
  let q ← getWaitQueue r
  setWaitQueue r { q with entries := q.entries ++ [{ e with exclusive := true }] }

/-- `remove_wait_queue` (wait.c:50-57): `__remove_wait_queue` (wait.h:205-208)
    is `list_del(&wq_entry->entry)`. The entry is identified by its `func`
    (each `eppoll_entry` sits on exactly one head); an entry that is not on
    the queue would be a `list_del` of an unlinked node, a mirror invariant
    failure. -/
def removeWaitQueue (r : WaitQueueRef) (e : WaitEntry) : M Unit := do
  let q ← getWaitQueue r
  let some i := q.entries.findIdx? (·.func == e.func)
    | invariant s!"remove_wait_queue: {repr e.func} is not on {repr r}"
  setWaitQueue r { q with entries := q.entries.eraseIdx i }

/-! ## The wake walk (wait.c:59-97) -/

/-! ## The wake walk (wait.c:59-97) and the callback it runs

`__wake_up_common` dispatches each entry's `func`; in tier 1 that is
`ep_poll_callback` (fs/eventpoll.c:1429-1534), which
re-enters the walk on the parent set's `poll_wait` head through
`ep_poll_safewake` (:815-819: `wake_up_poll`, so `__wake_up` →
`__wake_up_common_lock` → `__wake_up_common`). The recursion is the C's; Lean
cannot recurse mutually across modules, so the callback and
`ep_poll_safewake` live here with the walk, in one mutual group, and the
rest of the epoll mirror (`Leanux/FS/Eventpoll.lean`) calls them. The depth
is bounded by the nesting `ep_loop_check` admits at insert (at most
`EP_MAX_NESTS + 1` sets above a file), a fact of the state, not of the
syntax: the group carries that bound as fuel (`WAKE_NEST_FUEL`) and fails
noisily if it is exhausted (decision in docs/2026-10-12-epoll-design.md,
4.2) [AGENT 2026-10-12, stream S]. -/

/-- `EP_MAX_NESTS` (fs/eventpoll.c:220). -/
def EP_MAX_NESTS : Nat := 4
/-- `EPOLLINOUT_BITS` (fs/eventpoll.c:214). -/
def EPOLLINOUT_BITS : UInt32 := EPOLLIN ||| EPOLLOUT
/-- `EP_PRIVATE_BITS` (fs/eventpoll.c:212). -/
def EP_PRIVATE_BITS : UInt32 := EPOLLWAKEUP ||| EPOLLONESHOT ||| EPOLLET ||| EPOLLEXCLUSIVE
/-- `POLLFREE` (include/uapi/asm-generic/poll.h:30), `EPOLL_URING_WAKE`
    (include/uapi/linux/eventpoll.h:44). -/
def POLLFREE : UInt32 := 0x4000
def EPOLL_URING_WAKE : UInt32 := (1 : UInt32) <<< 27
/-- Nested wakes: a wake on a watched file reaches at most the sets above it,
    `EP_MAX_NESTS + 1` deep, each a walk; one more level is the walk of the
    file's own head. -/
def WAKE_NEST_FUEL : Nat := EP_MAX_NESTS + 2

mutual

/-- `curr->func(curr, mode, wake_flags, key)`: the entry's callback. `key` is
    the `void *`: `none` for NULL, `some m` for `poll_to_key(m)` (wait.h:224).
    The return is the C's `int`: negative stops the walk, non-zero counts
    against `nr_exclusive` for an exclusive entry. `sync` is
    `wake_flags & WF_SYNC` (wait.c:94 passes `wake_flags` as `sync`). -/
def WaitEntry.callAt (fuel : Nat) (e : WaitEntry) (mode wakeFlags : UInt32) (key : Option UInt32) : M Int :=
  match e.func with
  | .epPollCallback pwq => epPollCallbackAt fuel pwq mode wakeFlags key
termination_by (fuel, 3)

/-- `__wake_up_common` (wait.c:73-97), with the head's lock held: the walk
    over the entries, stopping when a callback returns negative, or when it
    returns non-zero for an exclusive entry and `--nr_exclusive` reaches
    zero (so `nr_exclusive = 0` never stops: `wake_up_all`). Returns the
    remaining `nr_exclusive`. -/
def wakeUpCommonAt (fuel : Nat) (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : M Int := do
  -- lockdep_assert_held(&wq_head->lock): a cut
  let q ← getWaitQueue r
  -- curr = list_first_entry(&wq_head->head, ...); `&curr->entry == &wq_head->head` (:80-83)
  if q.entries.isEmpty then return nrExclusive
  match fuel with
  | 0 => invariant s!"__wake_up_common: wakes nested deeper than {WAKE_NEST_FUEL} heads ({repr r})"
  | fuel + 1 =>
    -- list_for_each_entry_safe_from(curr, next, &wq_head->head, entry) (:85-94), over the
    -- snapshot (module doc)
    let mut nr := nrExclusive
    for curr in q.entries do
      let flags := curr.exclusive  -- unsigned flags = curr->flags
      let ret ← curr.callAt fuel mode wakeFlags key
      if ret < 0 then break
      -- `ret && (flags & WQ_FLAG_EXCLUSIVE) && !--nr_exclusive`
      if ret != 0 && flags then
        nr := nr - 1
        if nr == 0 then break
    if (← getWaitQueue r) != q then
      invariant s!"__wake_up_common: a callback edited the queue being walked ({repr r})"
    return nr
termination_by (fuel, 0)

/-- `ep_poll_safewake` as configured, without `CONFIG_DEBUG_LOCK_ALLOC`
    (fs/eventpoll.c:815-819): `wake_up_poll(&ep->poll_wait, EPOLLIN |
    pollflags)`, which is `__wake_up(.., TASK_NORMAL, 1, poll_to_key(m))`
    (wait.h:236-236, wait.c:124-127) and `__wake_up_common_lock` (:99-110)
    around the walk; `epi` is unused in this variant. -/
def epPollSafewakeAt (fuel : Nat) (ep : EpId) (_epi : Option EpiId) (pollflags : UInt32) : M Unit := do
  -- spin_lock_irqsave(&wq_head->lock, flags); the walk; spin_unlock_irqrestore
  discard <| wakeUpCommonAt fuel (.epPollWait ep) TASK_NORMAL 1 0 (some (EPOLLIN ||| pollflags))
termination_by (fuel, 1)

/-- `ep_poll_callback(wait, mode, sync, key)` (fs/eventpoll.c:1429-1534):
    `epi = ep_item_from_wait(wait)`, `pollflags = key_to_poll(key)` (0 for a
    NULL key). The set's lock is a cut; `ep_set_busy_poll_napi_id` (:1440)
    returns at `ep_busy_loop_on` (:610-613, both terms zero);
    `ep_pm_stay_awake_rcu` is empty without `CONFIG_PM`. In tier 1 no task
    sleeps on `ep->wq` (design 5), so the exclusive-wake rule (:1483-1502)
    is not reached: its arm stops. -/
def epPollCallbackAt (fuel : Nat) (pwqId : PwqId) (_mode wakeFlags : UInt32) (key : Option UInt32) : M Int := do
  let pwq ← getPwq pwqId
  let epiId := pwq.base
  let epi ← getEpi epiId
  let epId := epi.ep
  let pollflags := key.getD 0
  let mut pwake := 0
  let mut ewake : Int := 0
  -- spin_lock_irqsave(&ep->lock, flags)
  -- ep_set_busy_poll_napi_id(epi): `!ep_busy_loop_on(ep)` returns at once
  let ep ← getEp epId
  _ ← branchCmp .epBusyLoopOnUsecs (ep.busyPollUsecs != 0) ep.busyPollUsecs 0
  _ ← branch .epBusyLoopOnNet false   -- net_busy_loop_on(): sysctl_net_busy_poll is 0 (design 3.3)
  _ ← branch .epSetBusyPollNotOn true
  let skip ← do
    -- `!(epi->event.events & ~EP_PRIVATE_BITS)`: a disabled (fired oneshot) item
    if ← branchCmp .epPollCallbackDisabled (epi.events &&& ~~~EP_PRIVATE_BITS == 0) (epi.events &&& ~~~EP_PRIVATE_BITS).toNat 0 then
      pure true
    -- `pollflags && !(pollflags & epi->event.events)`
    else if ← branchCmp .epPollCallbackKey (pollflags != 0) pollflags.toNat 0 then
      branchCmp .epPollCallbackKeyMiss (pollflags &&& epi.events == 0) (pollflags &&& epi.events).toNat 0
    else pure false
  if !skip then
    let ep ← getEp epId
    if ← branch .epPollCallbackScanning ep.ovflist.isSome then
      -- :1467-1471, the item joins `ovflist` unless already there: a callback
      -- while the same set is being scanned needs a second task (design 9.3)
      invariant "ep_poll_callback while its set is scanning (the ovflist arm): a second task"
    else if ← branch .epPollCallbackNotLinked (!epi.linked) then
      -- list_add_tail(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake_rcu(epi)
      setEp epId { ep with rdllist := ep.rdllist ++ [epiId] }
      setEpi epiId { (← getEpi epiId) with linked := true }
    if ← branch .epPollCallbackWqActive (← waitqueueActive (.epWq epId)) then
      unsupported "a task sleeping on ep->wq at ep_poll_callback (tier 2)"
    if ← branch .epPollCallbackPollWaitActive (← waitqueueActive (.epPollWait epId)) then
      pwake := pwake + 1
  -- out_unlock: spin_unlock_irqrestore(&ep->lock, flags)
  if ← branch .epPollCallbackPwake (pwake != 0) then
    epPollSafewakeAt fuel epId (some epiId) (pollflags &&& EPOLL_URING_WAKE)
  if ← branchCmp .epPollCallbackNotExclusive (epi.events &&& EPOLLEXCLUSIVE == 0) (epi.events &&& EPOLLEXCLUSIVE).toNat 0 then
    ewake := 1
  if ← branchCmp .epPollCallbackPollfree (pollflags &&& POLLFREE != 0) (pollflags &&& POLLFREE).toNat 0 then
    unsupported "POLLFREE at ep_poll_callback (signalfd, binder: outside the domain)"
  let _ := wakeFlags
  return ewake
termination_by (fuel, 2)

end

/-- `__wake_up_common` at the top of a wake: the walk with the full nesting
    budget. -/
def wakeUpCommon (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : M Int :=
  wakeUpCommonAt WAKE_NEST_FUEL r mode nrExclusive wakeFlags key

/-- `ep_poll_safewake(ep, epi, pollflags)` from the epoll mirror's own
    call sites (`ep_insert`, `ep_modify`, `ep_clear_and_put`), with the full
    nesting budget. -/
def epPollSafewake (ep : EpId) (epi : Option EpiId) (pollflags : UInt32) : M Unit :=
  epPollSafewakeAt WAKE_NEST_FUEL ep epi pollflags

/-- `__wake_up_common_lock` (wait.c:99-110): the walk under the head's lock;
    returns how many exclusive entries were woken, `nr_exclusive - remaining`. -/
def wakeUpCommonLock (r : WaitQueueRef) (mode : UInt32) (nrExclusive : Int) (wakeFlags : UInt32)
    (key : Option UInt32) : M Int := do
  -- spin_lock_irqsave(&wq_head->lock, flags)
  let remaining ← wakeUpCommon r mode nrExclusive wakeFlags key
  -- spin_unlock_irqrestore(&wq_head->lock, flags)
  return nrExclusive - remaining

/-- `__wake_up` (wait.c:124-127). -/
def wakeUpBase (r : WaitQueueRef) (mode : UInt32) (nr : Int) (key : Option UInt32) : M Int :=
  wakeUpCommonLock r mode nr 0 key

/-- `__wake_up_locked_key` (wait.c:145-147): with the head's lock held. -/
def wakeUpLockedKey (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) : M Unit :=
  discard <| wakeUpCommon r mode 1 0 key

/-- `__wake_up_sync_key` (wait.c:167-172). The `!wq_head` test (:169) is a
    NULL check on a pointer the mirror holds as a `WaitQueueRef`, never NULL
    on these paths. -/
def wakeUpSyncKey (r : WaitQueueRef) (mode : UInt32) (key : Option UInt32) : M Unit :=
  discard <| wakeUpCommonLock r mode 1 WF_SYNC key

/-! ## The macros (wait.h:219-246); each drops `__wake_up`'s return -/

/-- `wake_up(x)` (wait.h:219). -/
def wakeUp (r : WaitQueueRef) : M Unit := discard <| wakeUpBase r TASK_NORMAL 1 none
/-- `wake_up_all(x)` (wait.h:221). -/
def wakeUpAll (r : WaitQueueRef) : M Unit := discard <| wakeUpBase r TASK_NORMAL 0 none
/-- `wake_up_sync(x)` (wait.h:224), `__wake_up_sync` (wait.c:203-205). -/
def wakeUpSync (r : WaitQueueRef) : M Unit := wakeUpSyncKey r TASK_NORMAL none
/-- `wake_up_interruptible(x)` (wait.h:226). -/
def wakeUpInterruptible (r : WaitQueueRef) : M Unit :=
  discard <| wakeUpBase r TASK_INTERRUPTIBLE 1 none
/-- `wake_up_interruptible_all(x)` (wait.h:228): `nr_exclusive = 0`. -/
def wakeUpInterruptibleAll (r : WaitQueueRef) : M Unit :=
  discard <| wakeUpBase r TASK_INTERRUPTIBLE 0 none
/-- `wake_up_poll(x, m)` (wait.h:236-236). -/
def wakeUpPoll (r : WaitQueueRef) (m : UInt32) : M Unit :=
  discard <| wakeUpBase r TASK_NORMAL 1 (some m)
/-- `wake_up_locked_poll(x, m)` (wait.h:240-240). -/
def wakeUpLockedPoll (r : WaitQueueRef) (m : UInt32) : M Unit :=
  wakeUpLockedKey r TASK_NORMAL (some m)
/-- `wake_up_interruptible_sync_poll(x, m)` (wait.h:244-244). -/
def wakeUpInterruptibleSyncPoll (r : WaitQueueRef) (m : UInt32) : M Unit :=
  wakeUpSyncKey r TASK_INTERRUPTIBLE (some m)

end Leanux
