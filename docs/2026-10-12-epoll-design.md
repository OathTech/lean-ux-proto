# Epoll over the FS slice — design, 2026-10-12

[AGENT, fork of the coordinator] A design, not a build: no mirror, guest or
kernel code is written here. It follows the kernel scout's recommendation
(`docs/2026-10-12-kernel-scout.md`, 4.1) and the simulation-target review's
rules for cuts and stops (`docs/2026-10-12-simulation-target-review.md`,
3.2 and 4.4), and it closes the wait-queue question the pipes reconnaissance
deferred (`docs/2026-10-05-pipes-reconnaissance.md`, "Why pipes, not
epoll"). Every kernel claim below was read in the configured source,
`.deps/linux` (6.12.110), with the line numbers given; none has been run
against a build yet, so section 11's first step is a measurement.

The scout's profile needs one correction (section 9.3): in a single-task
domain the `ovflist` is never populated, so that path is modelled as data
but not exercised.

## 1. Target

Mirror epoll as the C does it, over the files the slice already mirrors:

- `epoll_create1(flags)`;
- `epoll_ctl(epfd, ADD | MOD | DEL, fd, event)` where `fd` is an eventfd, a
  pipe end, another epoll file, or a fixture file (`/dev/null` at fds 0-7,
  which gives the `-EPERM` arm);
- `epoll_wait(epfd, events, maxevents, 0)`: timeout 0 only (section 9.1);
- the readiness callbacks that `write`, `read` and `close` on a watched file
  run synchronously inside the caller's task (`ep_poll_callback`);
- `close` and `dup` of epoll files and of watched files, including the
  release paths that unhook a watched file (`eventpoll_release_file`) and
  tear down an epoll set (`ep_clear_and_put`);
- nested epoll with its loop and reverse-path limits.

Everything is one task, as today: no blocking wait, no second thread, no
deferred unit on these paths. What this adds to the mirror, beyond epoll's
own control flow (edge- and level-triggered re-queueing, `EPOLLONESHOT`,
`EPOLLEXCLUSIVE`, nesting), is the **wait-queue service**: wait-queue
entries, their head/tail order, `__wake_up_common`'s walk and the callback
it runs. Today every `wake_up_*` on the pipe and eventfd paths is a comment
("no waiters"); after this design each is a call into a service that is
mirror code (section 4.2), which is the contract a later simulation proof
needs at that boundary.

## 2. The kernel paths, verified

All in `fs/eventpoll.c` unless named. `EP_MAX_NESTS` is 4 (:220),
`EP_MAX_EVENTS` is `INT_MAX / 12` (:222), `EP_PRIVATE_BITS` is
`EPOLLWAKEUP | EPOLLONESHOT | EPOLLET | EPOLLEXCLUSIVE` (:212),
`EPOLLEXCLUSIVE_OK_BITS` is `EPOLLIN | EPOLLOUT | EPOLLERR | EPOLLHUP |
EPOLLWAKEUP | EPOLLET | EPOLLEXCLUSIVE` (:216). The configured kernel has
`CONFIG_EPOLL=y`, `CONFIG_NET_RX_BUSY_POLL=y`, no `CONFIG_PM_SLEEP`, and
runs on one vCPU (`harness/linux.py`, `-smp 1`).

### 2.1 Creating an epoll file

`do_epoll_create` (:2398-2437): `flags & ~EPOLL_CLOEXEC` is `-EINVAL`
(:2408); `ep_alloc` (:1327-1349) is a `kzalloc` (a kind-305 site, section
3.1), `init_waitqueue_head` of `wq` and `poll_wait`, an empty `rdllist`,
`rbr = RB_ROOT_CACHED`, `ovflist = EP_UNACTIVE_PTR`, `user =
get_current_user()` (the `root_user` refcount: the operand-exclusion
precedent of `fs/pipe.c:794`), `refcount = 1`; then `get_unused_fd_flags`
(the mirror's `getUnusedFdFlags`), `anon_inode_getfile("[eventpoll]",
&eventpoll_fops, ep, O_RDWR | cloexec)` (the mirror's `allocFilePseudo`
path, as eventfd), `fd_install`. Failures unwind through
`ep_clear_and_put` and `put_unused_fd`. `eventpoll_fops` (:1271-1280):
`release`, `poll`, `llseek = noop_llseek`, `unlocked_ioctl`, `show_fdinfo`.

### 2.2 `epoll_ctl`: `do_epoll_ctl` (:2479-2608)

In order: `fdget(epfd)` else `-EBADF` (:2490); `fdget(fd)` else `-EBADF`
(:2495); `!file_can_poll(tf)` is `-EPERM` (:2499; `f_op->poll` NULL, true
of `/dev/null`); for ADD and MOD, `ep_take_care_of_epollwakeup` clears
`EPOLLWAKEUP` unconditionally without `CONFIG_PM_SLEEP` (:2461-2464);
`f == tf` or `!is_file_epoll(f)` is `-EINVAL` (:2510); `EPOLLEXCLUSIVE` is
`-EINVAL` on MOD, and on ADD when the target is an epoll file or the mask
has bits outside `EPOLLEXCLUSIVE_OK_BITS` (:2519-2523). Then, for ADD only
(:2552-2575): if the epoll file is itself watched (`f->f_ep`), or its
`gen == loop_check_gen`, or the target is an epoll file, the nested mutex
is taken, `loop_check_gen++`, `full_check = 1`, and for an epoll target
`ep_loop_check(ep, tep) != 0` is `-ELOOP` (:2562-2563). `ep_find` (:1356)
looks the pair `(tf, fd)` up; `error = -EINVAL` (:2579); the switch:

- ADD: absent, `events |= EPOLLERR | EPOLLHUP` then `ep_insert` (:2584);
  present, `-EEXIST` (:2586);
- DEL: present, `ep_remove`; absent, `-ENOENT` (:2597);
- MOD: present and not `EPOLLEXCLUSIVE`, `events |= EPOLLERR | EPOLLHUP`
  then `ep_modify` (:2602-2604); present and exclusive, the `-EINVAL`
  stands; absent, `-ENOENT` (:2607).

With `full_check`, `clear_tfile_check_list` (:2384) runs at the exit.

### 2.3 Insert

`ep_insert` (:1827-1906): `ep_alloc_epitem` (:1753-1777) compares the
user's `epoll_watches` against `max_user_watches` (`-ENOSPC`; section 3.4),
increments it, `kmem_cache_zalloc(epi_cache)` (`-ENOMEM`, :1768-1770),
sets `ffd = (tfile, fd)`, `event`. `ep_register_epitem` (:1794-1822):
`ep_attach_file` (:1709-1741) links the item at the head of the target's
`f_ep` list, allocating an `epitems_head` (`ephead_cache`, :1723) when the
target is not an epoll file and has none yet, an epoll target using its own
`refs`; with `full_check` and a non-epoll target, `list_file(tfile)`
(:425); `ep_rbtree_insert` (:1567); `ep_get(ep)`. Then `full_check &&
reverse_path_check()` is `-EINVAL` after `ep_remove` (:1850-1852).
`ep_item_poll(epi, &epq.pt, 1)` (:1219-1239) with the queue proc set:
`pt->_key = events`, `vfs_poll` (`include/linux/poll.h:88-93`:
`DEFAULT_POLLMASK` when `f_op->poll` is NULL, which `-EPERM` already
excludes) or `__ep_eventpoll_poll` for an epoll target, result masked by
`events`. The file's `poll` calls `poll_wait` (`poll.h:42-46`) on each of
its wait-queue heads, which calls `ep_ptable_queue_proc` (:1540-1565):
`kmem_cache_alloc(pwq_cache)` (:1547; on failure `epq->epi = NULL`, so
`ep_insert` removes the item and returns `-ENOMEM`, :1879),
`init_waitqueue_func_entry(&pwq->wait, ep_poll_callback)`, `pwq->whead`,
`pwq->base = epi`, then `add_wait_queue_exclusive` for `EPOLLEXCLUSIVE` or
`add_wait_queue` otherwise, and `pwq` pushed at the head of
`epi->pwqlist`. If `revents` is non-zero and the item is not linked, it goes
to the tail of `rdllist` (:1888); `wq` is woken if active (:1891-1892) and
an active `poll_wait` counts a `pwake` (:1893-1894), served by
`ep_poll_safewake(ep, NULL, 0)` after the lock (:1900-1901).

### 2.4 Modify and remove

`ep_modify` (:1910-1991): `events` and `data` are overwritten; `ep_item_poll`
with a NULL queue proc (no new registration, so an item keeps the exclusive
flag its entries were queued with); if ready and not linked, the tail of
`rdllist` (:1963), `wq` wake (:1967-1968), `pwake` (:1969-1970, :1976-1977).

`ep_remove` (:1074-1100): `ep_unregister_pollwait` (:844-854) walks
`pwqlist`, `remove_wait_queue` on each `whead` (:823-838) and frees the
entry; `epi->dying` (:1084, false in the domain); `epi_fget` (:1008-1016,
succeeds on a live file); `ep_remove_file` (:1022-1044): when the item is
the last on the file's `f_ep` the list head is cleared and, for a non-epoll
file, the `epitems_head` freed if unlisted; `ep_remove_epi` (:1046-1069):
`rb_erase_cached`, unlink from `rdllist` if linked, `kfree_rcu`,
`percpu_counter_dec`; the ep's refcount drops but not to zero.

### 2.5 The callback, and the wakeups that reach it

`ep_poll_callback(wait, mode, sync, key)` (:1429-1525), with `epi =
ep_item_from_wait(wait)` and `pollflags = key_to_poll(key)`:
`ep_set_busy_poll_napi_id` (:656, returns at once when busy polling is off);
an item with no bits outside `EP_PRIVATE_BITS` (a oneshot already fired) is
skipped (:1448); `pollflags && !(pollflags & events)` is skipped (:1451);
if the ep is scanning, the item is chained on `ovflist` (:1453-1458), else
if not linked it goes to the tail of `rdllist` (:1459-1462); with `wq`
active (:1482; never, in tier 1), the exclusive-wake rule by `EPOLLIN` /
`EPOLLOUT` (:1483-1495) and `wake_up_sync` or `wake_up` (:1500-1502); an
active `poll_wait` counts `pwake` (:1504-1505), served by
`ep_poll_safewake(ep, epi, pollflags & EPOLL_URING_WAKE)` (:1511-1512);
`ewake = 1` for a non-exclusive item (:1514-1515); `POLLFREE` (:1517, out
of scope). The return is `ewake`, which `__wake_up_common` uses.

`ep_poll_safewake` (:776-811 with lockdep, :815-819 without) is
`wake_up_poll(&ep->poll_wait, EPOLLIN | pollflags)` either way; the `nests`
field is a lock annotation.

The wake sites in the slice, each `__wake_up_common` with `nr_exclusive = 1`
unless stated (`kernel/sched/wait.c:73-97`, `include/linux/wait.h:219-247`):

- `fs/pipe.c` `pipe_read`: `wr_wait` with `EPOLLOUT | EPOLLWRNORM` (:381,
  :402), `rd_wait` with `EPOLLIN | EPOLLRDNORM` (:404); `pipe_write`:
  `rd_wait` (:577, :602; :601's `was_empty || pipe->poll_usage` is where
  `pipe_poll`'s `poll_usage = true` (:664) changes the write path), `wr_wait`
  (:605); `pipe_release`: `wake_up_interruptible_all` on both (:735-736,
  `nr_exclusive = 0`, key NULL, so :1451's test is skipped). All but the
  release are `wake_up_interruptible_sync_poll` (`WF_SYNC`).
- `fs/eventfd.c`: `eventfd_read`'s `wake_up_locked_poll(EPOLLOUT)` (:207),
  `eventfd_write`'s `wake_up_locked_poll(EPOLLIN)` (:274), both under
  `waitqueue_active`; `eventfd_release`'s `wake_up_poll(EPOLLHUP)` (:113),
  which runs after `eventpoll_release` has already removed every item
  (section 2.8), so its queue is empty.

The queueing order (`wait.c:17-36`): `add_wait_queue` clears the exclusive
flag and inserts at the head; `add_wait_queue_exclusive` sets it and
inserts at the tail. The walk (:73-97): from the head; stop when an entry's
function returns negative; stop when it returns non-zero for an exclusive
entry and `--nr_exclusive` reaches zero. Since `ep_poll_callback` returns 0
for an exclusive item whose `wq` has no sleeper, in tier 1 an exclusive
item never ends the walk: two exclusive epoll sets on one eventfd both
queue the event. That is the C's behaviour and a corpus target.

### 2.6 Waiting

`do_epoll_wait` (:2642-2682): `maxevents <= 0 || > EP_MAX_EVENTS` is
`-EINVAL`; `access_ok`; `fdget(epfd)` else `-EBADF`; `!is_file_epoll` is
`-EINVAL`; `ep_poll`. `ep_timeout_to_timespec` (:2105-2124) reads no clock
for timeout 0 (`tv_sec = tv_nsec = 0`); `ktime_get_ts64` (:2120) only for a
positive timeout; NULL for a negative one.

`ep_poll` (:2161-2283) with timeout 0: `timed_out = 1` (:2180); `eavail =
ep_events_available` (:2191; :576-582, `rdllist` non-empty or `ovflist` not
`EP_UNACTIVE_PTR`); if available, `ep_send_events` and return its count if
non-zero; then `timed_out` returns 0 (:2205). `ep_busy_loop` (:2208),
`signal_pending` (:2212), the exclusive wait on `wq` (:2252) and
`schedule_hrtimeout_range` (:2257) are not reached.

`ep_send_events` (:2058-2103): `fatal_signal_pending` is `-EINTR` (:2071,
never in the domain); `ep_start_scan` (:893-912) moves `rdllist` to a batch
and enters scanning; each item, while `res < maxevents`, through
`ep_deliver_event` (:1995-2056): `list_del_init` (:2017), `ep_item_poll`
with a NULL queue proc, dropped when not ready, `epoll_put_uevent`
(:2029; `-EFAULT` re-inserts at the batch head, :2036-2038, not reached
with the guest's buffer), `EPOLLONESHOT` keeps only the private bits
(:2042-2043), a level-triggered item returns to the tail of `rdllist`
(:2044-2052). `ep_done_scan` (:914-962): `ovflist` items are head-inserted
(LIFO to FIFO), the batch's leftovers spliced at the head, scanning ends,
`wq` woken if `rdllist` is non-empty and active. The order after a wait
whose `maxevents` was short is therefore: leftovers, then `ovflist` items,
then the level-triggered re-adds in delivery order. The next wait observes
it.

### 2.7 Nested epoll

An epoll file's `poll` is `__ep_eventpoll_poll` (:1176-1212): `poll_wait`
on its `poll_wait` head (the outer's registration), `ep_start_scan`, each
batch item `ep_item_poll`ed at `depth + 1`; the first ready item yields
`EPOLLIN | EPOLLRDNORM`; an item found not ready is unlinked from the inner
set's list (:1206); `ep_done_scan`. So an outer `epoll_wait` edits the
inner's ready list. Readiness propagates upward through the callback:
a write to an eventfd in the inner set queues it there and, with the
inner's `poll_wait` active, `ep_poll_safewake` runs the outer's
`ep_poll_callback` with key `EPOLLIN`.

`ep_loop_check` (:2364-2382): `inserting_into = ep`; `ep_loop_check_proc(to,
0)` (:2296-2334) walks the target's tree in key order, marking each visited
set with `loop_check_gen`; an epoll item that is the inserting set, or
beyond `EP_MAX_NESTS`, yields `EP_MAX_NESTS + 1`; other epoll items recurse;
non-epoll items are `list_file`d for the reverse check; a depth above
`EP_MAX_NESTS` fails. `ep_get_upwards_depth_proc(ep, 0)` (:2339-2351)
follows `refs` upward; `depth + 1 + upwards_depth > EP_MAX_NESTS` fails.
`reverse_path_check` (:1655-1669) runs `reverse_path_check_proc` (:1624-1643)
from each listed file, counting paths per nesting level against
`path_limits = {1000, 500, 100, 50, 10}` (:1602, :1605-1614). The limit arms
are unreachable under the fixture's `RLIMIT_NOFILE` of 32 (section 9.3).

### 2.8 Release

`ep_eventpoll_release` (:1164-1172) → `ep_clear_and_put` (:1102-1139): an
active `poll_wait` gets `ep_poll_safewake(ep, NULL, 0)` (:1107-1108; never
active here, since `eventpoll_release` already unhooked every watcher of
this file); every item in key order, `ep_unregister_pollwait` then
`ep_remove` (the `cond_resched`s are in task context, no record);
`ep_refcount_dec_and_test` → `ep_free` (:981-988).

`eventpoll_release_file` (:1287-1325) runs from `__fput` through
`eventpoll_release` (`include/linux/eventpoll.h`, already in the domain;
the mirror's `.eventpollReleaseLinked` branch, today `unsupported`) when a
file with a non-empty `f_ep` is closed for the last time: each item in
list order is marked dying, unregistered, unlinked from the file and the
tree. The `dispose && ep_refcount_dec_and_test` free is unreachable in the
domain (the set's own file holds a reference). Note the order in `__fput`:
`eventpoll_release` precedes `f_op->release`, so closing a pipe's write
end first removes that end's items and then `pipe_release`'s
`wake_up_interruptible_all` reaches the read end's items on `rd_wait`,
which the next `epoll_wait` polls as `EPOLLHUP` (`pipe_poll`,
`fs/pipe.c:657-705`): the hangup delivery, a corpus target.

### 2.9 The tree

`ep_find` (:1356-1378) and `ep_rbtree_insert` (:1567-1586) walk an rbtree
keyed by `ep_cmp_ffd` (:507-512): the `struct file` address first, the fd
second. `rb_insert_color`, `rb_erase_cached` and `rb_next` are
`lib/rbtree.o`, which KCOV does not instrument (`lib/Makefile:12`). The
walks themselves are instrumented (section 3.2).

## 3. Hidden inputs

### 3.1 Allocation sites (kind 305, the existing hook)

Four consumer frames, all task context, `GFP_KERNEL`, steerable: `ep_alloc`'s
`kzalloc` (:1331), `ep_alloc_epitem`'s `epi_cache` (:1766),
`ep_ptable_queue_proc`'s `pwq_cache` (:1547), `ep_attach_file`'s
`ephead_cache` (:1723). The anon-inode file and the fdtable are the
existing sites. The failure arms: `-ENOMEM` from `do_epoll_create`,
`ep_alloc_epitem`, `ep_attach_file`, and `ep_insert`'s `-ENOMEM` after an
`ep_remove` when a `pwq` allocation failed. `kfree_rcu` and the cache frees
are not recorded. The interface commit (section 11) assigns the
`AllocSite` ids.

### 3.2 The tree's key order: a record-only hook (kind 308) [AGENT]

The address of a `struct file` is slab placement: a hidden input, like an
allocation outcome, and it decides observable behaviour in three places:
the walk in `ep_find` and `ep_rbtree_insert`; the iteration order of
`ep_clear_and_put`, which fixes the order of the per-item decisions when an
epoll set with two or more items is closed (a common trace); and the
iteration order of `ep_loop_check_proc`, which decides which nested path is
examined first (the verdict is order-independent, the decision sequence is
not).

Proposal: a kind-308 record at `ep_rbtree_insert` carrying the `ffd.file`
address (8 bytes, at the site's return address, as the kind-306 records
are), one per `EPOLL_CTL_ADD`. The mirror keys its ordered map by
`(recorded address, fd)`, which is `ep_cmp_ffd` exactly, and checks that a
file's address is stable across its lifetime (`invariant` otherwise). Under
`AGENTS.md` "Oracle kernel changes" this is record-only, approved as a
class; it still needs the per-merge signoff with the new identity, and a
kernel rebuild (two profiles).

Rejected alternative: no record, with the mirror iterating in `FileId`
(allocation) order and the check reporting any disagreement. Slab reuse
makes the address order differ from allocation order whenever a file slot
is recycled, which the corpus does constantly (close, then create); a
silent dependence on placement is a fail-open default.

The walks of `ep_find` and `ep_rbtree_insert` are a separate matter: their
`kcmp` decisions follow the tree's *shape*, which the uninstrumented
rebalancing fixes. Two honest options:

- (b, recommended) an ordered-map cut: `ep_find` and `ep_rbtree_insert` are
  declared **cut functions** in `correspondence/kcov.json` (a new key,
  `cut_functions`): their lines may be covered without mirror decisions,
  and the `ep_cmp_ffd` operands at both are excluded. The mirror's lookup
  and insert give the same results; the `rb_first`/`rb_next` iterations in
  the listed callers follow the key order the record fixes. One small
  checker rule, which pays by naming the library boundary the review (3.2)
  asks every cut to name.
- (a) a C-shaped red-black tree in Lean (`__rb_insert`, `__rb_erase`, their
  recolouring), which reproduces the walks exactly. About 300 lines with
  no witnesses for the rebalancing itself. The fallback if (b)'s rule
  proves awkward.

### 3.3 What tier 1 does not read

No clock (timeout 0 skips :2120), no random, no deferred unit, no signal.
Every callback runs inside the calling syscall's KCOV window, so records
stay per-operation as today. `ep_busy_loop` is unreached; `ep_busy_loop_on`
(:610-613) is `busy_poll_usecs || net_busy_loop_on()`, both zero on the
fixture (an environment constant; `EPIOCSPARAMS` is out of scope).

### 3.4 `max_user_watches` and the per-user counter

`max_user_watches` is computed at boot from `si.totalram` (:2814-2815): a
fixture constant with the QEMU memory fixed in `harness/linux.py`. The
mirror carries it as a `Kernel` field; the guest reads
`/proc/sys/fs/epoll/max_user_watches` at fixture time and the run fails on
a mismatch (fail-closed, like the kernel identity). The compare is
`percpu_counter_compare` → `__percpu_counter_compare`
(`lib/percpu_counter.c`, instrumented): on one vCPU with batch 32 the
quick arm always decides (`|count - rhs| > 32`), so the function is listed
and modelled as the C's `count` plus one per-cpu delta, or its operands
excluded, which section 11's measurement decides.

## 4. The mirror

### 4.1 State (`Leanux/Kernel/Defs.lean`)

New, C-shaped:

```
inductive WaitFunc | epPollCallback (pwq : PwqId)      -- tier 2 adds task waiters
structure WaitEntry where func : WaitFunc; exclusive : Bool
structure WaitQueue where entries : List WaitEntry := []  -- head first
inductive WaitQueueRef
  | pipeRd (p : PipeId) | pipeWr (p : PipeId) | eventfdWqh (c : CtxId)
  | epWq (e : EpId) | epPollWait (e : EpId)
structure EppollEntry where whead : Option WaitQueueRef; base : EpiId
structure Epitem where
  ep : EpId; file : FileId; fd : Int
  fileAddr : Nat                      -- the kind-308 record, ep_cmp_ffd's key
  events : UInt32; data : UInt64
  linked : Bool := false              -- rdllink
  onOvflist : Bool := false
  pwqlist : List PwqId := []          -- head first, as `next` chains them
  dying : Bool := false
structure Eventpoll where
  wq : WaitQueue := {}; pollWait : WaitQueue := {}
  rdllist : List EpiId := []
  ovflist : Option (List EpiId) := none   -- none = EP_UNACTIVE_PTR
  items : TreeMap (Nat × Int) EpiId := {} -- the rbtree, keyed (fileAddr, fd)
  refs : List EpiId := []             -- outer items watching this set, head first
  refcount : Nat := 1
  gen : Nat := 0; loopCheckDepth : Nat := 0
  user : UserId := .root
inductive FEp | null | head (items : List EpiId) | epRefs (e : EpId)
```

`File.fEp : Bool` becomes `fEp : FEp` (`f_ep` is NULL, a non-epoll file's
`epitems_head`, or an epoll file's own `refs`). `PrivateData` gains
`.eventpoll (e : EpId)`, `FopsId` gains `.eventpoll` with the `Fops` of
:1271-1280. `PipeInodeInfo` gains `rdWait wrWait : WaitQueue`;
`EventfdCtx.waiters : Nat` becomes `wqh : WaitQueue`. `Kernel` gains `eps`,
`epis`, `pwqs` with their counters, the globals `loopCheckGen`,
`insertingInto : Option EpId`, `tfileCheckList : List FileId`,
`pathCount : Array Nat` (:1590-1602), `maxUserWatches`, and
`user.epollWatches` as the percpu counter of 3.4.

### 4.2 The wait-queue service and poll (`Leanux/FS/Wait.lean`, `Poll.lean`)

`Wait.lean` is `kernel/sched/wait.c` at the mirror's altitude:
`addWaitQueue` (:17-25), `addWaitQueueExclusive` (:28-36),
`removeWaitQueue` (:50-57), `wakeUpCommon q mode nrExclusive wakeFlags key`
(:73-97, the walk over a snapshot of the entries, each `WaitFunc` dispatched
to its callback, the two stop rules), and the wrappers the slice uses:
`wakeUp`, `wakeUpPoll`, `wakeUpSyncKey` (:167-173), `wakeUpLockedKey`
(:145-148), `wakeUpInterruptibleAll` (`nr_exclusive = 0`). The pipe and
eventfd wake comments become calls; with no entries the walk returns at
:82-83, so the existing corpus is unchanged, and the full check says so.

`Poll.lean`: `PollTable` is `{ qproc : Option EpiId, key : UInt32 }`, the
C's function pointer as the one value it can take here (`ep_ptable_queue_proc`
with its `epq.epi`); `pollWait fid q pt` (`poll.h:42-46`) registers when
`qproc` is set; `vfsPoll` (`poll.h:88-93`) dispatches on the file's fops:
`pipePoll` (`fs/pipe.c:657-705`, including `poll_usage := true`),
`eventfdPoll` (`fs/eventfd.c:118-174`), `epEventpollPoll`; a fops without
`poll` yields `DEFAULT_POLLMASK`.

### 4.3 Functions (`Leanux/FS/Eventpoll.lean`, new)

One Lean function per C function of section 2, same names: `epAlloc`,
`doEpollCreate`, `doEpollCtl`, `epFind` (the map lookup, under the cut),
`epRbtreeInsert` (consumes the kind-308 record, inserts), `epAllocEpitem`,
`epAttachFile`, `epRegisterEpitem`, `epInsert`, `epModify`, `epRemove`,
`epUnregisterPollwait`, `epRemoveFile`, `epRemoveEpi`, `epPollCallback`,
`epPtableQueueProc`, `epPollSafewake`, `epItemPoll`, `epEventpollPoll`,
`epEventsAvailable`, `epStartScan`, `epDoneScan`, `epDeliverEvent`,
`epSendEvents`, `epPoll` (the timeout-0 path; the others `unsupported`),
`doEpollWait`, `epLoopCheck`, `epLoopCheckProc`, `epGetUpwardsDepthProc`,
`reversePathCheck`, `reversePathCheckProc`, `pathCountInc`, `listFile`,
`clearTfileCheckList`, `epClearAndPut`, `epFree`, `eventpollReleaseFile`.
`Syscalls.lean`'s `dispatch` gains the three syscalls; `FileTable.lean`'s
`fputFinal` calls `eventpollReleaseFile` where it is `unsupported` today.

### 4.4 Decisions, operands and cuts

Every `if` of section 2 is a `branch` with a named decision, in C order;
the ones whose other arm the domain cannot reach stop fail-noisy:

- `unsupported`: a task sleeping on `ep->wq` (:1482, :1891, :1967, :2252),
  a pending signal (:2071, :2212), a non-zero timeout (section 9.1),
  `POLLFREE` (:1517), a target that is neither eventfd, pipe, epoll nor
  `/dev/null`.
- `invariant`: `epi->dying` (:1084), `epi_fget` failing (:1013), an active
  `poll_wait` at `ep_clear_and_put` (:1107), the `dispose` free at
  :1320, `ep_is_scanning` at a callback (:1453; section 9.3).

Operands compared as today (`branchCmp`) where the C compares values the
mirror holds: masks, `maxevents`, `res`, counts, depths. Excluded: the
`ep_cmp_ffd` addresses (3.2) and `root_user`'s refcount at `ep_alloc`
(the pipe precedent). Cuts, each named beside its helper as the review asks:
the rbtree (3.2), `kfree_rcu` and the slab frees (no effect on retained
state), `cond_resched` in task context (no record, no effect),
`mutex`/`spinlock` operations (one task).

### 4.5 Nested epoll

`epItemPoll` recurses through `epEventpollPoll` with `depth`, bounded by
the loop check at insert (a set cannot contain itself, directly or through
up to `EP_MAX_NESTS` levels), so the recursion is structurally bounded by
the state the mirror built: the review's requirement for traversals (4.4).
`epPollSafewake` runs the outer callbacks synchronously, as the C does.

### 4.6 What changes in the existing slice

`fEp`'s type; the two wait queues on pipes and the one on eventfds; the
wake comments becoming calls (`Pipe.lean` :297, :372-374, :491-494, :561;
`EventfdOps.lean` :46-51, :83-84, :116-117); `pipe_write`'s `poll_usage`
arm (:601) becoming reachable; `fputFinal`'s `eventpoll_release` arm.
Nothing in `Leanux/WG` changes.

## 5. Environment rules (`Leanux/Env.lean`)

Few, and all are consequences of the single-task domain rather than
fixture facts:

- no task ever sleeps in `epoll_wait`, so `ep->wq` is always empty and a
  wake of it is a no-op walk; the mirror keeps the queue as data and stops
  on the arm that would need a sleeper;
- no signal is pending;
- `max_user_watches` and `net.core.busy_poll = 0` are fixture constants
  (3.3, 3.4), verified at fixture time;
- nothing is scheduled: the epoll paths touch no deferred unit, so the
  existing idle-point rules (`idleTimers`, `afterXmit`) are unaffected.

## 6. Harness and guest

Three operations (`harness/trace.py` `FIELDS`, `OPCODES`; `contracts/trace-v1.md`;
`harness/guest.c`):

| Operation | Fields | Wire (`struct operation`) | Opcode |
| --- | --- | --- | --- |
| `epoll_create1` | `flags` | `b = flags`; a producer (`PRODUCERS`) | 27 |
| `epoll_ctl` | `epfd`, `cmd` (1 ADD, 2 DEL, 3 MOD), `fd`, `events`, `data` | `fd = epfd`, `newfd = fd`, `a = cmd`, `b = events`, `value = data` | 28 |
| `epoll_wait` | `epfd`, `maxevents`, `timeout` | `fd = epfd`, `a = maxevents`, `b = timeout` | 29 |

`epfd` and `fd` take the contract's descriptor forms (`literal`, `ref`,
`pipe`/`end`); the validator rejects `timeout ≠ 0` and `maxevents` outside
1..16 until tier 2 widens them. The guest fills the event buffer with
`0xa5`, calls the syscall, and reports the `ret × 12` bytes through the
read channel (`struct observation`: the first 64 bytes and the BLAKE2s
digest), so `userOut` is the packed `epoll_event` array and the existing
comparison applies; `data` is the trace's `u64` so the array is fully
predicted. The opcodes are the coordinator's to allocate in the interface
commit, as for the W streams.

`correspondence/kcov.json` gains the files `fs/eventpoll.c`,
`kernel/sched/wait.c`, `include/linux/wait.h`, `include/linux/poll.h`,
`lib/percpu_counter.c`; the functions of section 2 and of `wait.c`
(`__wake_up`, `__wake_up_common`, `__wake_up_common_lock`,
`__wake_up_sync_key`, `__wake_up_locked_key`, `add_wait_queue`,
`add_wait_queue_exclusive`, `remove_wait_queue`); the `cut_functions` key
(3.2); the two operand exclusions; and the kind-308 site. The fixture
check of `max_user_watches` goes in `harness/linux.py` beside the identity.

## 7. Generator and corpus

`scripts/epoll-corpus.py` writes `corpus/epoll/` (suite `epoll`), about 45
traces, one per target, in the pipes corpus's style:

- create: flags 0, `EPOLL_CLOEXEC`, an invalid flag; `dup` of an epoll fd;
- ctl errors: `EBADF` both ways, `EPERM` on fd 0, `EINVAL` on self and on a
  non-epoll `epfd`, `EEXIST`, `ENOENT` for DEL and MOD, the three
  `EPOLLEXCLUSIVE` rejections, `ELOOP` on self-insert and on a 2-cycle,
  a chain of 5 sets (`EP_MAX_NESTS`) and one of 6;
- readiness at insert: an empty eventfd (not ready), a written one
  (ready), a pipe read end empty and full, a write end full;
- callbacks: write then wait; read then wait (`EPOLLOUT`); level-triggered
  repeat; `EPOLLET` once; `EPOLLONESHOT` once then MOD re-arms; MOD
  changing the mask drops and restores readiness; DEL of a ready item;
- order: a dup'd eventfd added twice to one set (two entries on one head:
  LIFO order of non-exclusive entries); two sets on one eventfd, exclusive
  and not (both queue, section 2.5); `maxevents` short of the ready count
  (leftovers first, then re-adds);
- nesting: inner readiness propagated to the outer; an outer wait that
  prunes the inner's list; close of the inner while watched;
- release: close of a watched eventfd (`eventpoll_release_file`); close of
  a pipe write end delivering `EPOLLHUP` to the read end's watcher;
  `EPOLLERR` on a write end whose readers are gone; close of a set with
  three items (the key-order walk, the record at work);
- allocation failure at each of the four sites, steered (the A machinery).

`evaluator/generate.py` gains the `epoll` profile (suite `epoll-generated`):
random mixes over a pool of eventfds, pipes and up to three sets, weighted
towards `epoll_ctl`/`write`/`epoll_wait` triples, with the domain filter
rejecting what tier 1 does not model.

Sentinels (`scripts/pipes-mutants.py` grows an epoll block): one for the
new verdict channel, the wait-queue order (`addWaitQueue` inserting at the
tail), rejected only by the two-entries trace; a one-off mutant for the
kind-308 instrument (the mirror ignoring the address and ordering by
`FileId`), run at the claim point and reported in the commit, then
deleted. Mirror-logic mutants (a dropped level-triggered re-add, a oneshot
not disarmed) are what the differential check exists for and get no
sentinel.

## 8. Evidence: what pays for itself

Under `AGENTS.md` "Gates and speedbumps":

- gates: the build and unit tests (new cases for the wait service's walk
  and the trace validator); the full differential check on the new oracle,
  all suites, including the regression claim that the existing pipes and
  eventfd corpora are unchanged by the service; the kernel identity;
- speedbumps: the two mutants above; the existing control suites.

The claim point's commit message carries the counts and the user's
signoff; no bundle, no narrative.

## 9. Out of scope (fail-noisy), and why

### 9.1 The scoping of waits: tiers

**Tier 1 (this design): timeout 0.** `ep_poll` returns within the calling
task; every record is per-operation; nothing new is needed from the
kernel beyond 3.2.

**Tier 2: timeout > 0 and -1.** Not a kernel-side difficulty but a
modelling one. With one task and no events, a positive timeout is
deterministic (the task sleeps in `schedule_hrtimeout_range`, the hrtimer
fires in hardirq, `timed_out = 1`, return 0), but the sleep itself has no
witness: no record marks the task leaving and re-entering the CPU (the
scout's shared gap), the hrtimer's expiry runs where KCOV does not collect,
and `kernel/sched/core.c` is not in the domain. With -1, a second actor is
needed to wake the sleeper, which the single-thread guest cannot provide.
The honest encoding is a `sleep` cut with a record at `schedule()` for the
calling task, which the scheduler-loop work (review item 6, in progress)
is the natural home for. Until then a non-zero timeout is `unsupported`.
Estimate 0.15 WU once that record exists; a guest thread for the waker is
part of it.

### 9.2 Not modelled

`epoll_pwait`/`epoll_pwait2` (a sigmask: signals are not modelled);
`EPIOCSPARAMS`/`EPIOCGPARAMS`; sockets as targets (`napi_id`, busy poll);
pollable fixture files other than `/dev/null`; `POLLFREE` (signalfd, aio);
`EPOLLWAKEUP` with `CONFIG_PM_SLEEP` (off: the bit is cleared, which is
modelled). Each is `unsupported` at its decision.

### 9.3 Modelled but unexercised, and said so

- the `ovflist` (:1453-1458, :925-941): populated only by a callback that
  runs while the same set is being scanned, which needs a second CPU or
  thread. The scout counted it as substance; in this domain it is data of
  the right shape with its arm marked `invariant`. Tier 2's waker thread
  reaches it.
- the `reverse_path_check` limits: 500 watchers of one file at depth 1
  exceed `RLIMIT_NOFILE`; the count runs, the limit arm does not fire.
- `EPOLLEXCLUSIVE` ending a wake walk: needs a sleeper on `ep->wq` (tier 2).
- `-EFAULT` from `epoll_put_uevent`: the guest's buffer is valid.

## 10. Risks

1. **The kind-308 record is a kernel change** (record-only). It costs a
   rebuild of both profiles and a new identity, and lands only with
   signoff. If the user prefers no kernel change for now, tier 1 shrinks to
   sets of at most one item with `ep_find` under the cut, which loses the
   release walk and nesting: not recommended.
2. **The wait-queue service touches every pipe and eventfd wake site.** The
   regression claim (section 8) is the guard; the service with empty queues
   is a no-op by construction.
3. **The percpu counter** may need its operands excluded rather than
   modelled if the batch logic's comparisons prove noisy (3.4). The
   measurement decides before any mirror code is written.
4. **The function list grows by about 55 functions** across five files; the
   first check runs will surface unlisted helpers (`ep_item_from_wait`,
   `ep_pm_stay_awake`, `__pm_relax` with `CONFIG_PM` off, `noop_llseek`),
   which are inlined or branch-free and go in `branch_free_functions`.
5. **The cut-functions rule** is a new checker mechanism. It is small (a
   set-membership test where unlisted functions are reported) but it must
   not become a way to hide drift: only the two tree walks may use it.
6. **Observation width**: 16 events × 12 bytes exceed the 64-byte head;
   the digest covers the rest, as for reads.

## 11. Execution plan

| Step | Stream | Work | WU |
| --- | --- | --- | --- |
| 0 | coordinator | Measurement on the current oracle: three probe traces with `fs/eventpoll.c` and `wait.c` listed; the covered function set; the `percpu_counter` operands; confirmation that file addresses are not monotone after a close-and-create. | 0.02 |
| 1 | coordinator | The interface commit: opcodes 27-29, `AllocSite` and `HiddenSite` ids (a block 190-199), the `FEp`, `PrivateData.eventpoll`, `FopsId.eventpoll` and `WaitQueue` types, `cut_functions` in `kcov.json`. | 0.02 |
| 2 | Q | `Wait.lean`, `Poll.lean`; the pipe and eventfd wake sites as calls; the pipe and eventfd `poll` functions; the regression claim on the existing corpora. | 0.1 |
| 3 | R | The kind-308 hook in `gen-choice-stream.py`; the kernel rebuild; the guest's three operations and the fixture read of `max_user_watches`; the trace contract; the domain file; the one-off record mutant. | 0.1 |
| 4 | S | `Eventpoll.lean`, `dispatch`, the observation; depends on Q and the interface. | 0.25 |
| 5 | T | `epoll-corpus.py`, the generator profile, the wake-order sentinel, the claim point: full check on the new oracle, controls, sentinels, then one signoff. | 0.1 |

About 0.6 WU in all, at the top of the scout's band plus the record. Q and
R run in parallel after step 1; S starts when Q's regression claim passes;
T overlaps S's second half. Tier 2 is a separate design note once the
scheduler record exists.

## 12. File ownership

| Stream | Files |
| --- | --- |
| Q | `Leanux/FS/Wait.lean`, `Leanux/FS/Poll.lean` (new); the wake and poll sites in `Leanux/FS/Pipe.lean`, `Leanux/FS/EventfdOps.lean` |
| R | `kernel/patches/gen-choice-stream.py`, `kernel/identity-*.txt`, `harness/guest.c`, `harness/trace.py`, `harness/linux.py`, `contracts/trace-v1.md`, `correspondence/kcov.json`, `harness/steer.py` |
| S | `Leanux/FS/Eventpoll.lean` (new), `Leanux/FS/Syscalls.lean`, `Leanux/FS/FileTable.lean` (`fputFinal`), `Leanux/Runner.lean` (the observation) |
| T | `scripts/epoll-corpus.py`, `corpus/epoll/`, `evaluator/generate.py`, `scripts/pipes-mutants.py` |
| coordinator | `Leanux/Kernel/Defs.lean` (the interface commit), `docs/decisions.md` |

## 13. Decisions for the user

1. **Tier 1 scope: timeout 0 only**, blocking waits `unsupported` until a
   scheduler record exists (9.1). Recommended; the alternative, an
   unwitnessed sleep cut now, is the fail-open shape the review warns
   against.
2. **The kind-308 address record** (3.2): a record-only kernel change,
   approved as a class but a new oracle. Recommended. Without it, tier 1 is
   single-item sets (risk 1).
3. **The ordered-map cut with `cut_functions`** (3.2, option b) rather than
   a Lean red-black tree (option a). Recommended as the smaller and more
   honest boundary; (a) remains available.
4. **Nested epoll in tier 1.** Recommended: it is where the loop and
   reverse-path logic lives, and it costs about 0.05 WU of S.

Tactical choices made here under the user's standing delegation, recorded
in `docs/decisions.md`: the wire mapping and opcode proposal (6), the
`max_user_watches` fixture check (3.4), the sentinel set (7).
