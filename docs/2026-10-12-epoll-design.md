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

## 15. Audit [AGENT, independent audit 2026-10-12]

An independent read of this design against the configured source
(`.deps/linux`, 6.12.110: `fs/eventpoll.c`, `fs/eventfd.c`, `fs/pipe.c`,
`kernel/sched/wait.c`, `include/linux/{wait,poll,eventpoll,percpu_counter}.h`,
`lib/percpu_counter.c`, `lib/Makefile`), the configured options
(`kernel/config-x86_64-net-choice`), the mirror touchpoints named in 4.6,
the checker (`evaluator/check.py`, `correspondence/kcov.json`) and the guest
(`harness/guest.c`, `harness/linux.py`). No build, check or guest was run.
The design body above is unchanged; the findings are numbered by category
with a severity (blocking / should fix / nit) and evidence.

### 15.1 Kernel claims: what holds, what slipped, what was read elsewhere

Holds, as written:
- the definitions and function ranges of section 2 (`EP_MAX_NESTS` :220,
  `EP_PRIVATE_BITS` :212, `EPOLLEXCLUSIVE_OK_BITS` :216, `do_epoll_ctl`'s
  error order :2489-2607, `ep_insert` :1841-1901, `ep_modify` :1960-1977,
  `ep_remove` :1081-1099, `ep_deliver_event` :2017-2055, `ep_done_scan`'s
  head-insert of `ovflist` items :937 and head-splice of the leftovers :950,
  `__ep_eventpoll_poll` :1187-1210, the loop and upward checks :2296-2382);
- the tree key (`ep_cmp_ffd` :507, address first) and that no existing record
  carries the allocated pointer (kind 305 records outcome, flags, size and
  return addresses), so a record at `ep_rbtree_insert` is the smallest
  instrument that fixes the order of the three walks (3.2);
- tier-1 determinism: timeout 0 returns at :2111-2115 before the clock read
  at :2120, `ep_poll` returns at :2205 before `ep_busy_loop`, every callback
  runs in the caller's task, and `__fput` runs `eventpoll_release`
  (`fs/file_table.c:459`) before `f_op->release` (:467);
- the wait-queue rules (`wait.c:17-25` head insert, :28-36 tail insert with
  the exclusive flag, :73-97 the walk and its two stops, :167-173 the
  `WF_SYNC` variant) and the exclusive-item claim: `ep_poll_callback` returns
  `ewake = 0` for an exclusive item with no sleeper (:1514-1515), so the walk
  never stops on it;
- the hangup delivery: `pipe_poll` sets `EPOLLHUP` on `!writers &&
  f_pipe != w_counter` (:689); `pipe2` pipes have `w_counter = 1` (:821) and
  `f_pipe = 0` (:948, :958), both already in the mirror (`Defs.lean:194,
  :246`, `Pipe.lean:239`);
- `lib/rbtree.o` uninstrumented (`lib/Makefile:12`); no `CONFIG_PM`, no
  `CONFIG_DEBUG_LOCK_ALLOC`, `CONFIG_NR_CPUS=1`, `CONFIG_PREEMPT_NONE`.

Not re-verified here: `/dev/null`'s fops lack `poll` (a grep of
`drivers/char/mem.c`'s `null_fops` shows no `.poll` line; not read in full).

Read from another revision or inferred, not from 6.12.110 (the design's
opening claim that every line was read in the configured source does not
hold for these):
- `ep_poll_callback`'s inner lines (2.5, 4.4, 9.3): :1451 is :1457,
  :1453-1458 is :1466-1471, :1459-1462 is :1472-1475; the configured code
  chains through `epi_on_ovflist` / `ovflist_next` (:557-566);
- `ep_events_available` (2.6): the configured form is
  `!list_empty_careful(rdllist) || ep_is_scanning(ep) ||
  read_seqcount_retry(&ep->seq, seq)` (:576-582); the `ovflist` sentinel
  test is `ep_is_scanning` (:539-542), the seqcount disjunct is new (C3);
- the per-cpu counter (3.4, risk 3, section 6): `CONFIG_SMP` is not set
  (C2);
- `eventfd_read`'s wake at ":207" (2.5): that line is in
  `eventfd_ctx_remove_wait_queue` (C5);
- the reverse-path limits "unreachable under `RLIMIT_NOFILE` 32" (2.7, 9.3):
  reachable (C4);
- `ep_poll_safewake` "is `wake_up_poll` either way" (2.5): the lockdep variant
  (:776-811) is `wake_up_locked_poll` with two decisions; the configured
  kernel takes :815-819, so the effect is as stated (C9).

### 15.2 Correctness and hidden inputs

**C1 (blocking). `loop_check_gen` is boot-global state shared by the traces
of a chunk, and the first `EPOLL_CTL_ADD` of every guest boot takes the
full-check arm.** `static u64 loop_check_gen = 0` (:394); a fresh set has
`gen = 0` from `kzalloc`; `do_epoll_ctl` :2552 takes the full check on
`ep->gen == loop_check_gen`, true until the first full check has run
(:2558 and :2615 then leave the counter at 2, and every later generation is
unequal to any set's `gen`). The guest runs up to 100 traces per boot
(`evaluator/check.py:58`, `chunk_traces`) and does not use epoll itself
(`harness/guest.c`: no epoll call), so in each chunk the first ADD of the
first epoll trace runs the nested mutex, `list_file`, `reverse_path_check`
and `clear_tfile_check_list` and covers their lines; the same ADD in any
later trace does not. A mirror that is a function of one trace cannot
predict this, and the `branchCmp` operands of :2552, :2302 and :2344 carry
the absolute counter, which also differs per trace. The design's 4.1 lists
`loopCheckGen` as a plain global and says nothing of this. Remedy: a
fixture warm-up in the guest at boot (`epoll_create1`, ADD of a throwaway
eventfd, close both), stated as an environment rule in section 5 and
`Leanux/Env.lean`, so `loop_check_gen >= 2` before any trace and the arm is
dead in the domain; `loopCheckGen` modelled relative to an unknown base,
with the three comparisons' operands excluded (`operand_exclusions`, the
`root_user.__count` precedent) and their outcomes still checked. Blocking
for step 1 (the state) and step 3 (the guest), not for the record.

**C2 (should fix). `CONFIG_SMP` is not set: there is no per-cpu counter.**
`lib/percpu_counter.c` is built only under `CONFIG_SMP` (`lib/Makefile:201`);
`percpu_counter_compare` is the inline at `include/linux/percpu_counter.h:171-179`
(a two-way compare of `fbc->count` with `rhs`), `percpu_counter_inc`/`dec`
are plain adds, and `percpu_counter_batch` does not exist. 3.4, risk 3,
section 6's file list and step 0's "percpu_counter operands" measurement
all go: `user.epollWatches : Nat`, two `branchCmp`s inlined at
`ep_alloc_epitem` :1759-1760 with operands `(count, max_user_watches)`, no
exclusion, no measurement. Smaller than designed.

**C3 (should fix). `ep_events_available` reads `ep->seq`, which the mirror
state lacks.** :578-581: `read_seqcount_begin` then `read_seqcount_retry`;
`ep_start_scan` (:905, :910) and `ep_done_scan` (:942, :952) each bump the
sequence twice. With one task the retry is always false, but the compare's
operands are the sequence numbers. Add `seq : Nat` to `Eventpoll`, the four
increments, and the retry as a `branchCmp` whose true arm is `invariant`;
list `include/linux/seqlock.h` in `files` for the witness. Correct 2.5's
callback lines (15.1) at the same time, since they are the witnesses of
`epPollCallback`'s decisions.

**C4 (should fix). The reverse-path limits are reachable within 32 fds; 2.7
and 9.3 say the opposite.** `path_count_inc(depth)` (:1605-1614) counts
chains through the tiers of sets above a file, not watchers of the file:
`reverse_path_check_proc` (:1624-1643) recurses from each item of the file
into `epi->ep->refs` and counts once per chain whose top set has no
watcher. Five tiers of two sets each, fully connected (sets S1,S2 watch the
eventfd; O1,O2 watch both S; T watch both O; U watch both T; V1 watches both
U) give 16 chains at depth 4 against `path_limits[4] = 10` (:1602): the
second insert into V1 fails with `-EINVAL` after `ep_remove` (:1850-1852),
using 9 sets and 10 fds beyond the fixture's. Every insert on the way
passes the loop check (depth 3, plus 1, plus 0 upward, is not above 4).
Three tiers of five give 125 against `path_limits[2] = 100` with 15 sets.
Model the arm as reachable and add a corpus trace per fired depth (the
depth-4 one is the cheapest). The `depth > EP_MAX_NESTS` arm at :1629
stays unreachable (bounded by the loop check) and is an `invariant`.

**C5 (should fix). The eventfd wake lines.** `:207` is in
`eventfd_ctx_remove_wait_queue` (:198-211), a kernel-internal API no
syscall reaches; `eventfd_read`'s `wake_up_locked_poll(EPOLLOUT)` is :238
under the `waitqueue_active` at :237 (the mirror's
`eventfdReadWaitqueueActive`, `EventfdOps.lean:83`). `eventfd_signal_mask`'s
`wake_up_locked_poll(EPOLLIN | mask)` at :76 is internal too. State both as
outside the domain so stream R lists neither :60-80 nor :198-211 and the
record site mapping does not point into them.

**C6 (should fix). `tfile_check_list` holds a file reference the mirror
must carry.** `list_file` (:425-444) decides `!head->next` (:430) and takes
a reference with `atomic_long_inc_not_zero(&file->f_count)` (:438, a
decision whose operand is the count); `unlist_file` (:446-462, absent from
4.3) decides `p` (:451) and `!hlist_empty` (:454), frees the head when its
list is empty (:460) and releases the reference with `fput` (:461) at
`do_epoll_ctl`'s exit. Between the two, `ep_item_poll`'s `epi_fget` (:1013)
and `fput` (:1237) compare `f_count` with that extra reference, so a mirror
that skips the pair mis-predicts their operands under `full_check`. Add
`listFile`'s two decisions, `unlistFile`, and the reference in `fCount`.
`FEp.head` needs no "listed" flag: `v->next` non-null (:1037) is membership
of `tfileCheckList`, which `epRemoveFile` must consult for its free
decision. Also in `ep_attach_file`: the `!head` race arm (:1729-1731) is an
`invariant` and `free_ephead(to_free)` (:1739) a decision on a null pointer.

**C7 (should fix). Wake sites missed or under-described in 2.5.**
`pipe_resize_ring`'s `wake_up_interruptible(&pipe->wr_wait)` (`fs/pipe.c:1327`,
reached by `F_SETPIPE_SZ` through `fcntl`, opcode 7; the mirror's comment at
`Pipe.lean:561`) is not in the list or the corpus: its key is NULL, so
:1457's mask test is skipped and a write-end watcher is queued whatever its
mask, then re-polled at delivery (a resize that makes room in a watched
full pipe delivers `EPOLLOUT`). `pipe_release`'s two wakes are conditional
on `!readers != !writers` (:734, the mirror's `.pipeReleaseOneSide`,
`Pipe.lean:296`): closing the second end of a pipe wakes nothing, which the
hangup trace's close order depends on. :381 and :577 sit on the blocking
paths (each precedes a `wait_event_interruptible_exclusive`) and are tier 2.
The remaining pipe sites (:1104-:1221) are FIFO opens, outside the domain.

**C8 (should fix). Allocation-site lines, which fix the kind-305 return
addresses stream R maps.** `ep_alloc_epitem`'s `kmem_cache_zalloc` is :1764
(3.1's :1766 is the `percpu_counter_dec` on failure; the `-ENOMEM` arm is
:1765-1768); `ep_ptable_queue_proc`'s `kmem_cache_alloc` is :1550 (3.1's
:1547 is `unlikely(!epi)`, an `invariant` arm here since every domain file
registers one head); `ep_attach_file`'s `kmem_cache_zalloc` is :1722 (3.1's
:1723 is the `!to_free` test). `ep_alloc`'s `kzalloc` at :1331 is right.

**C9 (nit). Other line and wording slips.** `ep_timeout_to_timespec` is
:2104-2123; `do_epoll_ctl` ends :2619; `ep_insert` ends :1904;
`ep_clear_and_put` is :1102-1141; `ep_send_events` ends :2102. The
`EPOLLWAKEUP` tests at :1855 and :1927-1931 (constant false after :2461
cleared the bit) are decisions 2.3 and 2.4 do not list; `ep_done_scan`'s
`wq` test (:957) is missing from 4.4's `unsupported` list;
`ep_poll_safewake` as configured is :815-819 (15.1). `ep_remove_epi` always
returns true (:1068), so :1320's live decision is `ep_refcount_dec_and_test`,
a refcount compare, not a `dispose` flag. The two `cond_resched` calls
(:1120, :1135) are not record-free in general: a resched record (kind 302,
`check.py:306`) is written when `__cond_resched` schedules, which a tick
that woke a kernel thread can cause; treat them as the existing resched
points are treated rather than as "no record".

### 15.3 Altitude and shape, against the simulation-target review

**M1 (should fix). `ep_clear_and_put` is two whole-tree walks, and
`epClearAndPut` must keep both.** :1116-1121 unregisters every item's wait
entries in key order; :1131-1136 then runs `ep_remove` on each, which calls
`ep_unregister_pollwait` again on an emptied list (:1081) before the dying
test, `epi_fget`, `ep_remove_file` and `ep_remove_epi`. 2.8's "every item in
key order, `ep_unregister_pollwait` then `ep_remove`" reads as one walk; the
decision order differs (all unregistrations precede the first removal), and
a one-walk mirror would fail the coverage order. The ordered map gives both
walks the key order the record fixes, so the cut (3.2, option b) holds for
the three consumers named there.

**M2 (nit). The walk "over a snapshot" (4.2).** The C iterates the live
list with `list_for_each_entry_safe_from`; in the domain no callback edits
the queue being walked (`POLLFREE` is out of scope, and a nested
`ep_poll_safewake` walks a different head), so a snapshot is equivalent.
Say it as an `invariant` after the walk (the queue is the snapshot) rather
than relying on it silently; that keeps the C's shape visible for the
proof's boundary at this service.

**M3 (nit). Fields the C reads that 4.1 lacks.** `ep->seq` (C3);
`ep->busy_poll_usecs`, read by `ep_busy_loop_on` (:612) from
`ep_set_busy_poll_napi_id` on the insert and callback paths (:1440, :1885),
with `net_busy_loop_on()` as the fixture constant 3.3 names: carry
`busyPollUsecs : Nat := 0` as data so the two decisions have their operands.
`WaitFunc` with one constructor is right for tier 1; see S2 for its tier-2
shape.

### 15.4 Evidence under the gates regime

**E1 (should fix). `cut_functions` exempts nothing the checker rejects
today, so it is a new rule, not a small exemption.** The checker requires
that every covered `.c` line of an anchored file belongs to a listed
function (`unlisted_c_lines`, `check.py:743-756`) and that every mirror
decision's C function is listed or branch-free (`witness_table`,
`check.py:711-725`); a listed function in which the mirror emits no
decision is not reported, and operands are compared only at declared
mirror decisions. Listing `ep_find` and `ep_rbtree_insert` in `functions`
with no mirror decisions already does what 3.2 wants, and with no decision
there is nothing to exclude. The review (3.2) asks that each cut be named;
name it in `Eventpoll.lean` beside `epFind`/`epRbtreeInsert`. If the
coordinator wants the rule the design implies (a covered listed function
must emit a decision unless declared cut), it is a new check with its own
case under "Checks must pay for themselves": a dropped-function mutant it
alone rejects, and a home for decision-free helpers that
`branch_free_functions` (inlined decision owners, the opposite case) does
not provide. Either way `check.py:251` rejects unknown keys, fail-closed,
so a new key means editing the validator and `test_evaluation`.

**E2 (should fix). The wait-queue-order sentinel is a mirror-logic mutant
and gets no sentinel by section 7's own rule.** Inserting at the wrong end
of the list changes the delivery order the two-entries trace observes, so
the differential check rejects it with no new verdict channel involved;
the wait service is neither a record instrument nor a comparison class
(AGENTS.md, "Gates and speedbumps"). Drop it, keep the trace. The kind-308
one-off is the right and sufficient instrument mutant.

**E3 (nit). The kind-308 one-off needs a trace that slab reuse actually
reorders.** "The mirror ordering by `FileId`" is rejected only where the
address order differs from allocation order; the three-item close trace
must be preceded by a close-and-create so a recycled slot sits between
fresh ones, which is what step 0's last measurement establishes. Name that
trace as the mutant's subset.

**E4 (nit). The `max_user_watches` fixture check is required, not
optional, after C2:** the value is an operand at every ADD (:1759). The
warm-up of C1 belongs in the same fixture step, and the fixture row should
carry the value so a mismatch names both sides.

### 15.5 Scope and estimate

**S1 (should fix). Tier 1 grows by the reachable limit arms and shrinks by
the counter.** C4 adds two traces and keeps one `-EINVAL` arm live (about
0.02 WU in T); C1, C3, C6 and C7 add state, four functions' worth of
decisions, a guest fixture step and one trace (about 0.05 WU across R and
S); C2 removes the counter modelling and a measurement. Step 0 should
confirm C1 (the first ADD of a boot covers `reverse_path_check`) in place
of the percpu operands, and keep the slab-reuse probe. The total stays
about 0.6-0.65 WU; the ownership table (12) is unchanged except that
`Leanux/Env.lean` gains the warm-up rule (coordinator).

**S2 (nit). Tier 2's `WaitFunc`.** Blocking `eventfd_read`/`write`
(`wait_event_interruptible_locked_irq`, :230, :265) add non-exclusive task
entries at the head; `pipe_read`/`pipe_write` add exclusive entries at the
tail (`wait_event_interruptible_exclusive`, :390, :579); `ep_poll` adds an
exclusive entry with `ep_autoremove_wake_function` (:2232-2252). Each
returns a value `__wake_up_common`'s stop rules consume. 9.1 should say
that tier 2 adds a `taskWaiter` constructor with its function's return, so
the tier-1 `WaitEntry` is not shaped in a way that excludes it.

**S3 (nit). The ovflist stays unexercised (9.3) and the design's
correction of the scout is right:** `ep_is_scanning` is true only between
`ep_start_scan` and `ep_done_scan` of the same task, and no callback runs
in that window without a second context.

### 15.6 Whose decisions

**D1 (should fix). Only the kernel record needs the user, and only at the
merge.** Decision 2 is record-only under "Oracle kernel changes": approved
as a class, landing with the per-merge signoff and the new identity; it
needs no advance ruling and should be presented as the signoff point it is.
Decisions 1, 3 and 4 are tactical under the user's 2026-10-12 delegation
("you are empowered to make tactical decisions towards that") and change no
kernel behaviour or configuration; the coordinator makes them, records them
as [AGENT] in `docs/decisions.md`, and informs the user. The one choice that
is the user's is whether epoll is the next target at all (the scout's
ranking, already before the user). The warm-up fixture of C1 is a guest
change, tactical, recorded the same way.

**D2 (nit). The closing paragraph's tactical list** should drop the
sentinel set (E2 leaves the one-off only) and add the warm-up rule.

### 15.7 Severity summary

| Severity | Findings |
| --- | --- |
| blocking | C1 |
| should fix | C2, C3, C4, C5, C6, C7, C8, M1, E1, E2, S1, D1 |
| nit | C9, M2, M3, E3, E4, S2, S3, D2 |

The design's core holds: the record-only kind-308 hook is the smallest
instrument for the tree order, tier 1 is deterministic without a sleep
witness, the wait-queue service is the right boundary and the cut of the
rbtree is honest. The blocking item is a fixture fact the design did not
see; the rest are corrections to section 2 from a closer read of this
revision, one dropped mechanism (E1) and one dropped sentinel (E2).
