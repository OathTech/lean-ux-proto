# Epoll over the FS slice — design, 2026-10-12 (v2)

[AGENT, fork of the coordinator] A design, not a build: no mirror, guest or
kernel code is written here. It follows the kernel scout's recommendation
(`docs/2026-10-12-kernel-scout.md`, 4.1) and the simulation-target review's
rules for cuts and stops (`docs/2026-10-12-simulation-target-review.md`,
3.2 and 4.4), and it closes the wait-queue question the pipes reconnaissance
deferred (`docs/2026-10-05-pipes-reconnaissance.md`, "Why pipes, not
epoll"). Version 2 answers the independent audit (section 15) with the
dispositions in section 14; the body below is corrected in place. Every
line number in sections 2 and 3 was re-read in the configured source,
`.deps/linux` (6.12.110), for this revision, on 2026-10-12; nothing has yet
been run against a build, so section 11's first step is a measurement.

The scout's profile needs one correction (section 9.3): in a single-task
domain the `ovflist` is never populated, so that path is modelled as data
but not exercised.

## 1. Target

Mirror epoll as the C does it, over the files the slice already mirrors:

- `epoll_create1(flags)`;
- `epoll_ctl(epfd, ADD | MOD | DEL, fd, event)` where `fd` is an eventfd, a
  pipe end, another epoll file, or a fixture file (`/dev/null` at fds 0-7,
  whose `null_fops`, `drivers/char/mem.c:649-657`, has no `poll`, which
  gives the `-EPERM` arm);
- `epoll_wait(epfd, events, maxevents, 0)`: timeout 0 only (section 9.1);
- the readiness callbacks that `write`, `read`, `fcntl(F_SETPIPE_SZ)` and
  `close` on a watched file run synchronously inside the caller's task
  (`ep_poll_callback`);
- `close` and `dup` of epoll files and of watched files, including the
  release paths that unhook a watched file (`eventpoll_release_file`) and
  tear down an epoll set (`ep_clear_and_put`);
- nested epoll with its loop and reverse-path limits, both arms of each.

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

All in `fs/eventpoll.c` unless named; every range below was re-read for v2.
`EP_MAX_NESTS` is 4 (:220), `EP_MAX_EVENTS` is `INT_MAX / 12` (:222),
`EP_PRIVATE_BITS` is `EPOLLWAKEUP | EPOLLONESHOT | EPOLLET | EPOLLEXCLUSIVE`
(:212), `EPOLLEXCLUSIVE_OK_BITS` is `EPOLLIN | EPOLLOUT | EPOLLERR |
EPOLLHUP | EPOLLWAKEUP | EPOLLET | EPOLLEXCLUSIVE` (:216). The configured
kernel (`kernel/config-x86_64-net-choice`) has `CONFIG_EPOLL=y`,
`CONFIG_NET_RX_BUSY_POLL=y`, `CONFIG_NR_CPUS=1` with no `CONFIG_SMP`,
`CONFIG_PREEMPT_NONE=y`, no `CONFIG_PM`, no `CONFIG_PM_SLEEP`, no
`CONFIG_DEBUG_LOCK_ALLOC`, and runs on one vCPU (`harness/linux.py`,
`-smp 1`).

### 2.1 Creating an epoll file

`do_epoll_create` (:2398-2439): `flags & ~EPOLL_CLOEXEC` is `-EINVAL`
(:2408); `ep_alloc` (:1327-1349) is a `kzalloc` (:1331, a kind-305 site,
section 3.1), `init_waitqueue_head` of `wq` and `poll_wait`, an empty
`rdllist`, `rbr = RB_ROOT_CACHED`, `ovflist = EP_UNACTIVE_PTR`, `user =
get_current_user()` (the `root_user` refcount: the operand-exclusion
precedent of `fs/pipe.c:794`), `refcount = 1`; then `get_unused_fd_flags`
(the mirror's `getUnusedFdFlags`), `anon_inode_getfile("[eventpoll]",
&eventpoll_fops, ep, O_RDWR | cloexec)` (the mirror's `allocFilePseudo`
path, as eventfd), `fd_install`. Failures unwind through
`ep_clear_and_put` and `put_unused_fd`. `eventpoll_fops` (:1271-1280):
`release`, `poll`, `llseek = noop_llseek`, `unlocked_ioctl`, `show_fdinfo`.
A fresh set's `gen` is 0 from the `kzalloc` (section 3.5).

### 2.2 `epoll_ctl`: `do_epoll_ctl` (:2479-2619)

In order: `fdget(epfd)` else `-EBADF` (:2490); `fdget(fd)` else `-EBADF`
(:2495); `!file_can_poll(tf)` is `-EPERM` (:2499; `f_op->poll` NULL, true
of `/dev/null`); for ADD and MOD, `ep_take_care_of_epollwakeup` clears
`EPOLLWAKEUP` unconditionally without `CONFIG_PM_SLEEP` (:2461-2464);
`f == tf` or `!is_file_epoll(f)` is `-EINVAL` (:2510); `EPOLLEXCLUSIVE` is
`-EINVAL` on MOD, and on ADD when the target is an epoll file or the mask
has bits outside `EPOLLEXCLUSIVE_OK_BITS` (:2519-2523). Then, for ADD only
(:2552-2575): if the epoll file is itself watched (`f->f_ep`), or `ep->gen
== loop_check_gen` (the boot-global `static u64 loop_check_gen` of :394;
section 3.5), or the target is an epoll file, the nested mutex is taken,
`loop_check_gen++` (:2558), `full_check = 1`, and for an epoll target
`ep_loop_check(ep, tep) != 0` is `-ELOOP` (:2562-2563). `ep_find`
(:1356-1378) looks the pair `(tf, fd)` up; `error = -EINVAL` (:2579); the
switch:

- ADD: absent, `events |= EPOLLERR | EPOLLHUP` then `ep_insert` (:2584);
  present, `-EEXIST` (:2586);
- DEL: present, `ep_remove`; absent, `-ENOENT` (:2597);
- MOD: present and not `EPOLLEXCLUSIVE`, `events |= EPOLLERR | EPOLLHUP`
  then `ep_modify` (:2602-2604); present and exclusive, the `-EINVAL`
  stands; absent, `-ENOENT` (:2607).

At the exit (:2612-2617), with `full_check`: `clear_tfile_check_list`
(:2384-2394), `loop_check_gen++` again (:2615), the nested mutex released.
So one full check leaves the counter two higher, and a set visited during
a check holds the odd intermediate value.

`list_file` (:425-444) and `unlist_file` (:446-462) carry state the mirror
must hold. `list_file`, called on every non-epoll file a check reaches
(:2327, :1813): if the file's `epitems_head` is not yet listed (`!head->next`,
:430) it takes a reference, `atomic_long_inc_not_zero(&file->f_count)`
(:438, a decision whose operand is the count), and pushes the head.
`unlist_file`, from `clear_tfile_check_list`: decides `p` (:451) and
`!hlist_empty` (:454), frees the head when its list is empty (:460), and
`fput`s the reference (:461). Between the two, `ep_item_poll`'s `epi_fget`
(:1013) and `fput` (:1237) compare `f_count` with that extra reference.

### 2.3 Insert

`ep_insert` (:1827-1904): `ep_alloc_epitem` (:1753-1777) compares the
user's `epoll_watches` against `max_user_watches` (:1759-1760, `-ENOSPC`;
section 3.4), increments it, `kmem_cache_zalloc(epi_cache)` (:1764;
`-ENOMEM` with the decrement, :1765-1768), sets `ffd = (tfile, fd)`,
`event`. `ep_register_epitem` (:1794-1822): `ep_attach_file` (:1709-1741)
links the item at the head of the target's `f_ep` list, allocating an
`epitems_head` (`ephead_cache`, :1722; `!to_free` is `-ENOMEM`, :1723)
when the target is not an epoll file and has none yet, an epoll target
using its own `refs`; the `!head` arm under the lock (:1729-1731) is a race
with a concurrent attach, unreachable here; `free_ephead(to_free)` (:1739)
decides on a null pointer. With `full_check` and a non-epoll target,
`list_file(tfile)` (:1813); `ep_rbtree_insert` (:1567-1586); `ep_get(ep)`.
Then `full_check && reverse_path_check()` is `-EINVAL` after `ep_remove`
(:1850-1852). `EPOLLWAKEUP` is tested (:1855), constant false after :2461.
`ep_item_poll(epi, &epq.pt, 1)` (:1219-1239) with the queue proc set:
`pt->_key = events`, `vfs_poll` (`include/linux/poll.h:88-93`:
`DEFAULT_POLLMASK` when `f_op->poll` is NULL, which `-EPERM` already
excludes) or `__ep_eventpoll_poll` for an epoll target, result masked by
`events`. The file's `poll` calls `poll_wait` (`poll.h:42-46`) on each of
its wait-queue heads, which calls `ep_ptable_queue_proc` (:1540-1565): the
`!epi` test (:1547) fires only when an earlier head's entry failed, and
every domain file has one head; `kmem_cache_alloc(pwq_cache)` (:1550; on
failure `epq->epi = NULL`, so `ep_insert` removes the item and returns
`-ENOMEM`, :1879); `init_waitqueue_func_entry(&pwq->wait,
ep_poll_callback)`, `pwq->whead`, `pwq->base = epi`, then
`add_wait_queue_exclusive` for `EPOLLEXCLUSIVE` or `add_wait_queue`
otherwise, and `pwq` pushed at the head of `epi->pwqlist`. `ep_insert` and
`ep_poll_callback` both call `ep_set_busy_poll_napi_id` (:1885, :1440),
which returns at `ep_busy_loop_on` (:610-613: `busy_poll_usecs ||
net_busy_loop_on()`, both zero). If `revents` is non-zero and the item is
not linked, it goes to the tail of `rdllist` (:1888); `wq` is woken if
active (:1891-1892) and an active `poll_wait` counts a `pwake`
(:1893-1894), served by `ep_poll_safewake(ep, NULL, 0)` after the lock
(:1900-1901).

### 2.4 Modify and remove

`ep_modify` (:1910-1980): `events` and `data` are overwritten; the
`EPOLLWAKEUP` arms (:1927-1931) are constant false; `ep_item_poll` with a
NULL queue proc (no new registration, so an item keeps the exclusive flag
its entries were queued with); if ready and not linked, the tail of
`rdllist` (:1963), `wq` wake (:1967-1968), `pwake` (:1969-1970,
:1976-1977).

`ep_remove` (:1074-1100): `ep_unregister_pollwait` (:844-854) walks
`pwqlist`, `remove_wait_queue` on each `whead` (:823-838) and frees the
entry; `epi->dying` (:1084, false in the domain); `epi_fget` (:1008-1016,
succeeds on a live file); `ep_remove_file` (:1022-1044): when the item is
the last on the file's `f_ep` the list head is cleared and, for a non-epoll
file, the `epitems_head` freed unless it is on `tfile_check_list`
(`v->next`, :1037); `ep_remove_epi` (:1046-1069): `rb_erase_cached`,
unlink from `rdllist` if linked, `kfree_rcu`, `percpu_counter_dec`, and it
always returns true (:1068); the ep's refcount drops but not to zero.

### 2.5 The callback, and the wakeups that reach it

`ep_poll_callback(wait, mode, sync, key)` (:1429-1525), with `epi =
ep_item_from_wait(wait)` and `pollflags = key_to_poll(key)`:
`ep_set_busy_poll_napi_id` (:1440); an item with no bits outside
`EP_PRIVATE_BITS` (a oneshot already fired) is skipped (:1448);
`pollflags && !(pollflags & events)` is skipped (:1457); if the set is
scanning (`ep_is_scanning`, :539-542: `ovflist != EP_UNACTIVE_PTR`) the
item is chained on `ovflist` unless already there (`epi_on_ovflist`,
:557-560; :1466-1471), else if not linked it goes to the tail of `rdllist`
(:1472-1475); with `wq` active (:1482; never, in tier 1), the
exclusive-wake rule by `EPOLLIN` / `EPOLLOUT` (:1483-1495) and
`wake_up_sync` or `wake_up` (:1500-1502); an active `poll_wait` counts
`pwake` (:1504-1505), served by `ep_poll_safewake(ep, epi, pollflags &
EPOLL_URING_WAKE)` (:1511-1512); `ewake = 1` for a non-exclusive item
(:1514-1515); `POLLFREE` (:1517, out of scope). The return is `ewake`,
which `__wake_up_common` uses.

`ep_poll_safewake` as configured (no `CONFIG_DEBUG_LOCK_ALLOC`) is
:815-819, `wake_up_poll(&ep->poll_wait, EPOLLIN | pollflags)`; the lockdep
variant (:776-811) is not compiled.

The wake sites in the domain, each `__wake_up_common` with
`nr_exclusive = 1` unless stated (`kernel/sched/wait.c:73-97`,
`include/linux/wait.h:219-247`):

- `fs/pipe.c` `pipe_read`: `wr_wait` with `EPOLLOUT | EPOLLWRNORM` (:402),
  `rd_wait` with `EPOLLIN | EPOLLRDNORM` (:404); `pipe_write`: `rd_wait`
  (:602; :601's `was_empty || pipe->poll_usage` is where `pipe_poll`'s
  `poll_usage = true` (:664) changes the write path), `wr_wait` (:605).
  These are `wake_up_interruptible_sync_poll` (`WF_SYNC`). The two sites
  on the blocking paths, :381 (before `wait_event_interruptible_exclusive`
  at :390) and :577 (before :579), are tier 2.
- `fs/pipe.c` `pipe_release`: `wake_up_interruptible_all` on both heads
  (:735-736, `nr_exclusive = 0`, key NULL, so :1457's test is skipped),
  only when `!readers != !writers` (:734; the mirror's
  `.pipeReleaseOneSide`, `Pipe.lean:296`): closing the second end of a pipe
  wakes nothing, which fixes the close order of the hangup trace.
- `fs/pipe.c` `pipe_resize_ring`: `wake_up_interruptible(&pipe->wr_wait)`
  (:1327), reached by `fcntl(F_SETPIPE_SZ)` (:1409, :1371; the mirror's
  comment at `Pipe.lean:561`), key NULL: a write-end watcher is queued
  whatever its mask and re-polled at delivery, so a resize that makes room
  in a watched full pipe delivers `EPOLLOUT`.
- `fs/eventfd.c`: `eventfd_read`'s `wake_up_locked_poll(EPOLLOUT)` (:238)
  under `waitqueue_active` (:237; the mirror's
  `.eventfdReadWaitqueueActive`, `EventfdOps.lean:83`); `eventfd_write`'s
  `wake_up_locked_poll(EPOLLIN)` (:274) under :273; `eventfd_release`'s
  `wake_up_poll(EPOLLHUP)` (:113), which runs after `eventpoll_release`
  has already removed every item (section 2.8), so its queue is empty.
  `eventfd_signal_mask` (:56-79, its wake at :76) and `eventfd_ctx_remove_wait_queue`
  (:198-211) are in-kernel APIs no syscall reaches: outside the domain, not
  listed.
- The FIFO sites (`fs/pipe.c:1104-1221`) are outside the domain.

The queueing order (`wait.c:17-36`): `add_wait_queue` clears the exclusive
flag and inserts at the head; `add_wait_queue_exclusive` sets it and
inserts at the tail. The walk (:73-97): from the head over the live list
(`list_for_each_entry_safe_from`); stop when an entry's function returns
negative; stop when it returns non-zero for an exclusive entry and
`--nr_exclusive` reaches zero. Since `ep_poll_callback` returns 0 for an
exclusive item whose `wq` has no sleeper, in tier 1 an exclusive item never
ends the walk: two exclusive epoll sets on one eventfd both queue the
event. That is the C's behaviour and a corpus target.

### 2.6 Waiting

`do_epoll_wait` (:2642-2682): `maxevents <= 0 || > EP_MAX_EVENTS` is
`-EINVAL`; `access_ok`; `fdget(epfd)` else `-EBADF`; `!is_file_epoll` is
`-EINVAL`; `ep_poll`. `ep_timeout_to_timespec` (:2104-2123) returns at
:2111-2115 for timeout 0 (`tv_sec = tv_nsec = 0`) before the clock read
`ktime_get_ts64` (:2120) a positive timeout makes; NULL for a negative one.

`ep_poll` (:2161-2283) with timeout 0: `timed_out = 1` (:2180); `eavail =
ep_events_available` (:2191). That function (:576-582) is
`read_seqcount_begin(&ep->seq)`, then `!list_empty_careful(&ep->rdllist)
|| ep_is_scanning(ep) || read_seqcount_retry(&ep->seq, seq)`: the retry
compares sequence numbers that `ep_start_scan` (:905, :910) and
`ep_done_scan` (:942, :952) each bump twice, so the mirror carries `seq`
(section 4.1); with one task the retry is always false. If available,
`ep_send_events` and return its count if non-zero; then `timed_out`
returns 0 (:2205). `ep_busy_loop` (:2208), `signal_pending` (:2212), the
exclusive wait on `wq` (:2252) and `schedule_hrtimeout_range` (:2257) are
not reached.

`ep_send_events` (:2058-2102): `fatal_signal_pending` is `-EINTR` (:2071,
never in the domain); `ep_start_scan` (:893-912) moves `rdllist` to a batch
and enters scanning; each item, while `res < maxevents`, through
`ep_deliver_event` (:1995-2056): `list_del_init` (:2017), `ep_item_poll`
with a NULL queue proc, dropped when not ready, `epoll_put_uevent`
(:2029; `-EFAULT` re-inserts at the batch head, :2036-2038, not reached
with the guest's buffer), `EPOLLONESHOT` keeps only the private bits
(:2042-2043), a level-triggered item returns to the tail of `rdllist`
(:2044-2052). `ep_done_scan` (:914-962): `ovflist` items are head-inserted
(:925-941, the `list_add` at :937, LIFO to FIFO), the batch's leftovers
spliced at the head (:950), scanning ends, `wq` woken if `rdllist` is
non-empty and active (:957). The order after a wait whose `maxevents` was
short is therefore: leftovers, then `ovflist` items, then the
level-triggered re-adds in delivery order. The next wait observes it.

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
0)` (:2296-2334) returns a set's cached depth when `ep->gen ==
loop_check_gen` (:2302, a set already visited in this check: a diamond),
else marks it and walks its tree in key order; an epoll item that is the
inserting set, or beyond `EP_MAX_NESTS`, yields `EP_MAX_NESTS + 1`; other
epoll items recurse; non-epoll items are `list_file`d (:2327) for the
reverse check; a depth above `EP_MAX_NESTS` fails.
`ep_get_upwards_depth_proc(ep, 0)` (:2339-2351) follows `refs` upward with
the same `gen` test (:2344); `depth + 1 + upwards_depth > EP_MAX_NESTS`
fails.

`reverse_path_check` (:1655-1669) runs `reverse_path_check_proc`
(:1624-1643) from each listed file: for each item watching the file, if the
item's set has no watcher (`hlist_empty(&epi->ep->refs)`) the chain is
counted at the current depth by `path_count_inc` (:1605-1614), else the
walk recurses into the set's watchers at `depth + 1`; `path_limits =
{1000, 500, 100, 50, 10}` (:1602), depth 0 unlimited. The count is over
chains through the tiers of sets above the file, not over watchers of the
file, so **the limits are reachable within the fixture's `RLIMIT_NOFILE` of
32**: five tiers of two sets, fully connected (S1, S2 watch the eventfd;
O1, O2 watch both S; T1, T2 both O; U1, U2 both T; V1 both U) give 16
chains at depth 4 against the limit of 10, so V1's second ADD fails with
`-EINVAL` after `ep_remove` (:1850-1852), using nine sets and ten fds; the
loop check passes at every step (depth 3, plus 1, plus 0 upward). Three
tiers of five sets give 125 chains at depth 2 against 100, with fifteen
sets. The `depth > EP_MAX_NESTS` arm (:1629) stays unreachable, bounded by
the loop check: an `invariant`.

### 2.8 Release

`ep_eventpoll_release` (:1164-1172) → `ep_clear_and_put` (:1102-1141): an
active `poll_wait` gets `ep_poll_safewake(ep, NULL, 0)` (:1107-1108; never
active here, since `eventpoll_release` already unhooked every watcher of
this file); then **two whole-tree walks in key order**: first
`ep_unregister_pollwait` on every item (:1116-1121), then `ep_remove` on
every item (:1131-1136), each `ep_remove` calling `ep_unregister_pollwait`
again on an emptied list (:1081) before the dying test, `epi_fget`,
`ep_remove_file` and `ep_remove_epi`; the decision order is all
unregistrations, then all removals. The `cond_resched` in each walk
(:1120, :1135) is a resched point like the existing ones (a kind-302 record
when `__cond_resched` schedules), not record-free. Then
`ep_refcount_dec_and_test` → `ep_free` (:981-988).

`eventpoll_release_file` (:1287-1325) runs from `__fput` through
`eventpoll_release` (`fs/file_table.c:459`, before `f_op->release` at
:467; `include/linux/eventpoll.h:34`, already in the domain; the mirror's
`.eventpollReleaseLinked` branch, today `unsupported`) when a file with a
non-empty `f_ep` is closed for the last time: each item in list order is
marked dying, unregistered, unlinked from the file and the tree. Since
`ep_remove_epi` always returns true, the decision at :1320 is
`ep_refcount_dec_and_test`, a refcount compare whose zero arm is
unreachable in the domain (the set's own file holds a reference). The
`__fput` order means closing a pipe's write end first removes that end's
items and then `pipe_release`'s `wake_up_interruptible_all` (the read end
still open, so :734 holds) reaches the read end's items on `rd_wait`, which
the next `epoll_wait` polls as `EPOLLHUP` (`pipe_poll`, `fs/pipe.c:657-705`,
the test at :689; `w_counter = 1` from :821 and `f_pipe = 0` from :948 and
:958 are already mirror state): the hangup delivery, a corpus target.

### 2.9 The tree

`ep_find` (:1356-1378) and `ep_rbtree_insert` (:1567-1586) walk an rbtree
keyed by `ep_cmp_ffd` (:507-512): the `struct file` address first, the fd
second. `rb_insert_color`, `rb_erase_cached` and `rb_next` are
`lib/rbtree.o`, which KCOV does not instrument (`lib/Makefile:12`). The
walks themselves are instrumented (section 3.2).

## 3. Hidden inputs

### 3.1 Allocation sites (kind 305, the existing hook)

Four consumer frames, all task context, `GFP_KERNEL`, steerable, with the
lines the kind-305 return-address map needs: `ep_alloc`'s `kzalloc`
(:1331), `ep_alloc_epitem`'s `kmem_cache_zalloc(epi_cache)` (:1764),
`ep_ptable_queue_proc`'s `kmem_cache_alloc(pwq_cache)` (:1550),
`ep_attach_file`'s `kmem_cache_zalloc(ephead_cache)` (:1722). The
anon-inode file and the fdtable are the existing sites. The failure arms:
`-ENOMEM` from `do_epoll_create`, `ep_alloc_epitem` (:1765-1768),
`ep_attach_file` (:1723), and `ep_insert`'s `-ENOMEM` (:1879) after an
`ep_remove` when a `pwq` allocation failed. `kfree_rcu` and the cache frees
are not recorded. The interface commit (section 11) assigns the
`AllocSite` ids.

### 3.2 The tree's key order: a record-only hook (kind 308) [AGENT]

The address of a `struct file` is slab placement: a hidden input, like an
allocation outcome, and it decides observable behaviour in three places:
the walk in `ep_find` and `ep_rbtree_insert`; the iteration order of
`ep_clear_and_put`'s two walks, which fixes the order of the per-item
decisions when a set with two or more items is closed (a common trace);
and the iteration order of `ep_loop_check_proc`, which decides which
nested path is examined first (the verdict is order-independent, the
decision sequence is not).

Proposal: a kind-308 record at `ep_rbtree_insert` carrying the `ffd.file`
address (8 bytes, at the site's return address, as the kind-306 records
are), one per `EPOLL_CTL_ADD`. The mirror keys its ordered map by
`(recorded address, fd)`, which is `ep_cmp_ffd` exactly, and checks that a
file's address is stable across its lifetime (`invariant` otherwise). Under
`AGENTS.md` "Oracle kernel changes" this is record-only, approved as a
class; it lands with the per-merge signoff, the new identity and the patch
hash recorded, after a kernel rebuild (two profiles).

Rejected alternative: no record, with the mirror iterating in `FileId`
(allocation) order and the check reporting any disagreement. Slab reuse
makes the address order differ from allocation order whenever a file slot
is recycled, which the corpus does constantly (close, then create); a
silent dependence on placement is a fail-open default.

The walks of `ep_find` and `ep_rbtree_insert` are a separate matter: their
`kcmp` decisions follow the tree's *shape*, which the uninstrumented
rebalancing fixes. The ordered-map cut needs no checker change: both
functions are listed in `correspondence/kcov.json` `functions` and the
mirror emits no decision inside them. The checker reports a covered line
only when its function is unlisted (`unlisted_c_lines`,
`evaluator/check.py:743-756`) and compares operands only at declared mirror
decisions (`witness_table`, :711-725), so a listed function with no
decisions is exactly a cut, with nothing to exclude. The cut is named in
`Eventpoll.lean` beside `epFind` and `epRbtreeInsert`, as the review (3.2)
asks: inputs the key, result the item or its absence, no retained state
beyond the map, the `rb_first`/`rb_next` iterations of the listed callers
following the key order the record fixes. The alternative, a C-shaped
red-black tree in Lean (about 300 lines, no witnesses for the rebalancing
itself), stays available if a later proof wants the shape.

### 3.3 What tier 1 does not read

No clock (timeout 0 returns before :2120), no random, no deferred unit, no
signal. Every callback runs inside the calling syscall's KCOV window, so
records stay per-operation as today. `ep_busy_loop` is unreached;
`ep_busy_loop_on` (:610-613) reads `ep->busy_poll_usecs` (data, zero) and
`sysctl_net_busy_poll` (a fixture constant, zero; `EPIOCSPARAMS` is out of
scope).

### 3.4 `max_user_watches` and the per-user counter

`max_user_watches` is computed at boot from `si.totalram` (:2814-2815): a
fixture constant with the QEMU memory fixed in `harness/linux.py`. Without
`CONFIG_SMP` there is no per-cpu counter: `lib/percpu_counter.c` is not
built (`lib/Makefile:201`), `percpu_counter_compare` is the inline at
`include/linux/percpu_counter.h:171-179` (a two-way compare of
`fbc->count` with `rhs`) and `percpu_counter_inc`/`dec` are plain adds. The
mirror carries `user.epollWatches : Nat` and `maxUserWatches : Nat`, and
`ep_alloc_epitem`'s compare is two `branchCmp`s inlined at :1759-1760 with
operands `(count, max_user_watches)`, no exclusion. Because the value is an
operand at every ADD, the fixture check is required: the guest reads
`/proc/sys/fs/epoll/max_user_watches` at fixture time, the fixture row
carries the value, and the run fails on a mismatch naming both sides
(fail-closed, like the kernel identity).

### 3.5 Boot-global state: `loop_check_gen` [v2, audit C1]

`loop_check_gen` (:394) is a static shared by every trace of a guest boot;
the checker runs up to 100 traces per boot (`evaluator/check.py:58`,
`chunk_traces`) and the guest makes no epoll call of its own. A fresh set
has `gen = 0`, so the first ADD of a boot takes the full-check arm at
:2552 (`ep->gen == loop_check_gen`, 0 against 0), runs the nested mutex,
`list_file`, `reverse_path_check` and `clear_tfile_check_list`, and leaves
the counter at 2; the same ADD in any later trace of the chunk does not. A
mirror that is a function of one trace cannot predict which trace is
first, and the operands at :2552, :2302 and :2344 carry the absolute
counter, which differs per trace.

Remedy, in two parts:

- a **fixture warm-up** in the guest at boot (`epoll_create1`, ADD of a
  throwaway eventfd, close both), in the same fixture step as the
  `max_user_watches` read, stated as an environment rule (section 5): the
  counter is at least 2 before any trace, so a fresh set's `gen` of 0 never
  equals it, and a set visited during a check holds an odd value that the
  even counter after the check never equals: the `ep->gen ==
  loop_check_gen` arm at :2552 is dead in the domain (`invariant`), and
  :2302 and :2344 fire only within one check, on a diamond;
- `loopCheckGen` modelled **relative** to an unknown boot base (2 at the
  start of every trace, the increments as the C's), with the operands of
  the three comparisons excluded (`operand_exclusions`, the
  `root_user.__count` precedent) and their outcomes checked as usual.
  Equality is preserved by the shift: sets created in a trace have `gen` 0
  in both, and sets marked in a trace carry base-plus-relative in the
  kernel and relative in the mirror.

## 4. The mirror

### 4.1 State (`Leanux/Kernel/Defs.lean`)

New, C-shaped:

```
inductive WaitFunc | epPollCallback (pwq : PwqId)      -- tier 2 adds taskWaiter
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
  onOvflist : Bool := false           -- ovflist_next != EP_UNACTIVE_PTR
  pwqlist : List PwqId := []          -- head first, as `next` chains them
  dying : Bool := false
structure Eventpoll where
  wq : WaitQueue := {}; pollWait : WaitQueue := {}
  rdllist : List EpiId := []
  ovflist : Option (List EpiId) := none   -- none = EP_UNACTIVE_PTR (not scanning)
  seq : Nat := 0                      -- ep->seq, bumped twice per start and done scan
  items : TreeMap (Nat × Int) EpiId := {} -- the rbtree, keyed (fileAddr, fd)
  refs : List EpiId := []             -- outer items watching this set, head first
  refcount : Nat := 1
  gen : Nat := 0; loopCheckDepth : Nat := 0
  busyPollUsecs : Nat := 0
  user : UserId := .root
inductive FEp | null | head (items : List EpiId) | epRefs (e : EpId)
```

`File.fEp : Bool` becomes `fEp : FEp` (`f_ep` is NULL, a non-epoll file's
`epitems_head`, or an epoll file's own `refs`); a head's membership of
`tfile_check_list` is the `Kernel` list below (the C's `head->next`), which
`epRemoveFile` consults for its free decision (:1037). `PrivateData` gains
`.eventpoll (e : EpId)`, `FopsId` gains `.eventpoll` with the `Fops` of
:1271-1280. `PipeInodeInfo` gains `rdWait wrWait : WaitQueue`;
`EventfdCtx.waiters : Nat` becomes `wqh : WaitQueue`. `Kernel` gains `eps`,
`epis`, `pwqs` with their counters, the globals `loopCheckGen : Nat := 2`
(relative, 3.5), `insertingInto : Option EpId`, `tfileCheckList : List
FileId` (the listed heads, newest first, each holding one `fCount`
reference), `pathCount : Array Nat` (:1590-1602), `maxUserWatches : Nat`,
and `user.epollWatches : Nat`.

### 4.2 The wait-queue service and poll (`Leanux/FS/Wait.lean`, `Poll.lean`)

`Wait.lean` is `kernel/sched/wait.c` at the mirror's altitude:
`addWaitQueue` (:17-25), `addWaitQueueExclusive` (:28-36),
`removeWaitQueue` (:50-57), `wakeUpCommon q mode nrExclusive wakeFlags key`
(:73-97: the walk over the live list, each `WaitFunc` dispatched to its
callback, the two stop rules), and the wrappers the slice uses: `wakeUp`,
`wakeUpPoll`, `wakeUpSyncKey` (:167-173), `wakeUpLockedKey` (:145-148),
`wakeUpInterruptibleAll` (`nr_exclusive = 0`), `wakeUpInterruptible`. The
C walks the live list; in the domain no callback edits the queue being
walked (`POLLFREE` is out of scope, a nested `ep_poll_safewake` walks a
different head), so the mirror walks a snapshot and asserts after the walk
that the queue is still that snapshot (`invariant`), keeping the C's shape
visible at this boundary rather than relying on it silently. The pipe and
eventfd wake comments become calls; with no entries the walk returns at
:82-83, so the existing corpus is unchanged, and the full check says so.

**The callback's module [AGENT, stream S 2026-10-12].** `ep_poll_callback`
re-enters the walk through `ep_poll_safewake` (`wake_up_poll` on the parent
set's `poll_wait`), a mutual recursion Lean cannot express across modules.
The callback and `ep_poll_safewake` therefore live in `Wait.lean`, in one
`mutual` group with `__wake_up_common`, and `Eventpoll.lean` calls them;
`ep_ptable_queue_proc` likewise lives in `Poll.lean`, where `poll_wait`
calls it. The group's recursion is bounded by the nesting `ep_loop_check`
admits, a fact of the state, so the walk carries that bound as fuel
(`WAKE_NEST_FUEL = EP_MAX_NESTS + 2` heads) and stops `invariant` if it is
exhausted; `ep_item_poll`/`__ep_eventpoll_poll` carry the same bound. The
alternative, parameterising the walk by a callback dispatcher, would have
moved the C's call graph into every wake site's arguments.

`Poll.lean`: `PollTable` is `{ qproc : Option EpiId, key : UInt32 }`, the
C's function pointer as the one value it can take here (`ep_ptable_queue_proc`
with its `epq.epi`); `pollWait fid q pt` (`poll.h:42-46`) registers when
`qproc` is set; `vfsPoll` (`poll.h:88-93`) dispatches on the file's fops:
`pipePoll` (`fs/pipe.c:657-705`, including `poll_usage := true`),
`eventfdPoll` (`fs/eventfd.c:118-174`), `epEventpollPoll`; a fops without
`poll` yields `DEFAULT_POLLMASK`.

### 4.3 Functions (`Leanux/FS/Eventpoll.lean`, new)

One Lean function per C function of section 2, same names: `epAlloc`,
`doEpollCreate`, `doEpollCtl`, `epFind` and `epRbtreeInsert` (the cut,
named there; the latter consumes the kind-308 record), `epAllocEpitem`,
`epAttachFile`, `epRegisterEpitem`, `epInsert`, `epModify`, `epRemove`,
`epUnregisterPollwait`, `epRemoveFile`, `epRemoveEpi`, `epPollCallback`,
`epPtableQueueProc`, `epPollSafewake`, `epSetBusyPollNapiId`, `epItemPoll`,
`epEventpollPoll`, `epEventsAvailable`, `epStartScan`, `epDoneScan`,
`epDeliverEvent`, `epSendEvents`, `epPoll` (the timeout-0 path; the others
`unsupported`), `doEpollWait`, `epLoopCheck`, `epLoopCheckProc`,
`epGetUpwardsDepthProc`, `reversePathCheck`, `reversePathCheckProc`,
`pathCountInc`, `listFile`, `unlistFile`, `clearTfileCheckList`,
`epClearAndPut` (both walks, section 2.8), `epFree`, `eventpollReleaseFile`.
`Syscalls.lean`'s `dispatch` gains the three syscalls; `FileTable.lean`'s
`fputFinal` calls `eventpollReleaseFile` where it is `unsupported` today.

### 4.4 Decisions, operands and cuts

Every `if` of section 2 is a `branch` with a named decision, in C order,
including the constant-false `EPOLLWAKEUP` tests (:1855, :1927-1931), the
`ep_set_busy_poll_napi_id` tests (:1440, :1885), `list_file`'s two (:430,
:438), `unlist_file`'s two (:451, :454), and the seqcount retry (:581). The
ones whose other arm the domain cannot reach stop fail-noisy:

- `unsupported`: a task sleeping on `ep->wq` (:957, :1482, :1891, :1967,
  :2252), a pending signal (:2071, :2212), a non-zero timeout (section
  9.1), `POLLFREE` (:1517), a target that is neither eventfd, pipe, epoll
  nor `/dev/null`, a `pwq` registration on a second head (:1547).
- `invariant`: `epi->dying` (:1084), `epi_fget` failing (:1013), an active
  `poll_wait` at `ep_clear_and_put` (:1107), the refcount reaching zero at
  :1320, `ep_is_scanning` at a callback (:1466; section 9.3), the seqcount
  retry (:581), the first-ADD arm at :2552 (3.5), `ep_attach_file`'s race
  arm (:1729), `reverse_path_check_proc`'s depth arm (:1629).

Operands compared as today (`branchCmp`) where the C compares values the
mirror holds: masks, `maxevents`, `res`, counts, depths, `f_count` with
the `tfile_check_list` reference included, the watch count against
`max_user_watches`. Excluded: the `loop_check_gen` comparisons (:2552,
:2302, :2344; 3.5) and `root_user`'s refcount at `ep_alloc` (the pipe
precedent). The `ep_cmp_ffd` comparisons sit inside the cut and are not
mirror decisions, so nothing is excluded there. Cuts, each named beside its
helper as the review asks: the rbtree (3.2), `kfree_rcu` and the slab frees
(no effect on retained state), `mutex`/`spinlock` operations (one task).
The `cond_resched` calls of `ep_clear_and_put` go through the existing
resched rule.

### 4.5 Nested epoll

`epItemPoll` recurses through `epEventpollPoll` with `depth`, bounded by
the loop check at insert (a set cannot contain itself, directly or through
up to `EP_MAX_NESTS` levels), so the recursion is structurally bounded by
the state the mirror built: the review's requirement for traversals (4.4).
`epPollSafewake` runs the outer callbacks synchronously, as the C does.
`reversePathCheck` runs the real limits, and its `-EINVAL` arm is live
(2.7).

### 4.6 What changes in the existing slice

`fEp`'s type; the two wait queues on pipes and the one on eventfds; the
wake comments becoming calls (`Pipe.lean` :297, :372-374, :491-494, :561;
`EventfdOps.lean` :46-51, :83-84, :116-117); `pipe_write`'s `poll_usage`
arm (:601) becoming reachable; `fputFinal`'s `eventpoll_release` arm.
Nothing in `Leanux/WG` changes.

Built (stream S): `__fput` and `__fput_sync` moved from `FileTable.lean` to
a new `Leanux/FS/Fput.lean` after `Eventpoll.lean`, with the `f_op->release`
dispatcher, because `__fput` runs `eventpoll_release_file` and an epoll
file's release, which run `fput` and the whole slice: the module order
follows the C's call graph. `File.fEp` is `FEp` (NULL, a head's items, a
set's `refs`); `Kernel` gains the three stores, the statics of
fs/eventpoll.c and the `ep_pqueue`'s live `epi`; `UserStruct` gains
`epollWatches`. Line numbers in the mirror are the pristine source's: the
check reads statements and spans from `.deps/linux`, so a patch of an
anchored file must keep its line count (every existing one does; section
16).

## 5. Environment rules (`Leanux/Env.lean`)

Few, and all are consequences of the single-task domain or fixture facts:

- **the warm-up** (3.5): the guest's fixture has run one `epoll_create1`,
  one ADD of a throwaway eventfd and two closes before the first trace, so
  `loop_check_gen` is at least 2 and every set a trace creates starts with
  `gen` 0 below it; the mirror's counter is relative;
- no task ever sleeps in `epoll_wait`, so `ep->wq` is always empty and a
  wake of it is a no-op walk; the mirror keeps the queue as data and stops
  on the arm that would need a sleeper;
- no signal is pending;
- `max_user_watches` (3.4) and `net.core.busy_poll = 0` (3.3) are fixture
  constants, the former verified at fixture time;
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

The guest's fixture gains one step before the first trace of a boot: the
warm-up ADD (3.5) and the read of `/proc/sys/fs/epoll/max_user_watches`,
reported in the fixture row; `harness/linux.py` checks the value beside the
identity (3.4).

`correspondence/kcov.json` gains the files `fs/eventpoll.c`,
`kernel/sched/wait.c`, `include/linux/wait.h`, `include/linux/poll.h`,
`include/linux/seqlock.h`; the functions of section 2, `ep_find` and
`ep_rbtree_insert` among them (decision-free, the cut of 3.2), and those of
`wait.c` (`__wake_up`, `__wake_up_common`, `__wake_up_common_lock`,
`__wake_up_sync_key`, `__wake_up_locked_key`, `add_wait_queue`,
`add_wait_queue_exclusive`, `remove_wait_queue`); the three
`loop_check_gen` operand exclusions and the `root_user` one; the kind-308
site. No new key: `check.py:251` rejects unknown keys and none is needed.

## 7. Generator and corpus

`scripts/epoll-corpus.py` writes `corpus/epoll/` (suite `epoll`), about 50
traces, one per target, in the pipes corpus's style:

- create: flags 0, `EPOLL_CLOEXEC`, an invalid flag; `dup` of an epoll fd;
- ctl errors: `EBADF` both ways, `EPERM` on fd 0, `EINVAL` on self and on a
  non-epoll `epfd`, `EEXIST`, `ENOENT` for DEL and MOD, the three
  `EPOLLEXCLUSIVE` rejections, `ELOOP` on self-insert and on a 2-cycle,
  a chain of 5 sets (`EP_MAX_NESTS`) and one of 6;
- reverse-path limits (2.7): the depth-4 construction of nine sets whose
  last ADD is `-EINVAL`, and the depth-2 one of fifteen; a diamond (two
  sets watching one eventfd, one set watching both) for the :2302 and
  :2344 arms;
- readiness at insert: an empty eventfd (not ready), a written one
  (ready), a pipe read end empty and full, a write end full;
- callbacks: write then wait; read then wait (`EPOLLOUT`); level-triggered
  repeat; `EPOLLET` once; `EPOLLONESHOT` once then MOD re-arms; MOD
  changing the mask drops and restores readiness; DEL of a ready item;
  `F_SETPIPE_SZ` making room in a watched full pipe (`EPOLLOUT` through
  the key-NULL wake, 2.5);
- order: a dup'd eventfd added twice to one set (two entries on one head:
  LIFO order of non-exclusive entries); two sets on one eventfd, exclusive
  and not (both queue, section 2.5); `maxevents` short of the ready count
  (leftovers first, then re-adds);
- nesting: inner readiness propagated to the outer; an outer wait that
  prunes the inner's list; close of the inner while watched;
- release: close of a watched eventfd (`eventpoll_release_file`); close of
  a pipe write end while the read end stays open, delivering `EPOLLHUP` to
  the read end's watcher (the :734 condition); `EPOLLERR` on a write end
  whose readers are gone; close of a set with three items after a
  close-and-create so a recycled file slot sits between two fresh ones
  (`close_three_recycled`: the two walks of 2.8 in the recorded order);
- allocation failure at each of the four sites, steered (the A machinery).

`evaluator/generate.py` gains the `epoll` profile (suite `epoll-generated`):
random mixes over a pool of eventfds, pipes and up to three sets, weighted
towards `epoll_ctl`/`write`/`epoll_wait` triples, with the domain filter
rejecting what tier 1 does not model.

Mutants: one **one-off** for the kind-308 instrument, the mirror ignoring
the recorded address and ordering by `FileId`, whose subset is
`close_three_recycled` (the only trace where slab reuse puts the address
order out of allocation order, which step 0 confirms); run at the claim
point, reported in the commit, then deleted. No sentinel is added: a wrong
insertion end in the wait service changes the delivery order the
two-entries trace observes and the differential check rejects it with no
new verdict channel involved, so by the gates regime it is mirror logic,
not an instrument.

## 8. Evidence: what pays for itself

Under `AGENTS.md` "Gates and speedbumps":

- gates: the build and unit tests (new cases for the wait service's walk
  and the trace validator); the full differential check on the new oracle,
  all suites, including the regression claim that the existing pipes and
  eventfd corpora are unchanged by the service; the kernel identity;
- speedbumps: the kind-308 one-off (section 7); the existing control
  suites and sentinels, unchanged.

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

Tier 2 widens `WaitFunc` with a `taskWaiter` constructor carrying its
function's return value, which `__wake_up_common`'s stop rules consume:
blocking `eventfd_read`/`eventfd_write` add non-exclusive entries at the
head (`wait_event_interruptible_locked_irq`, `fs/eventfd.c:230`, :265);
`pipe_read`/`pipe_write` add exclusive entries at the tail
(`wait_event_interruptible_exclusive`, `fs/pipe.c:390`, :579); `ep_poll`
adds an exclusive entry with `ep_autoremove_wake_function` (:2232-2252).
The tier-1 `WaitEntry` is shaped so that this is an added constructor, not
a reshaping. Estimate 0.15 WU once the sleep record exists; a guest thread
for the waker is part of it.

### 9.2 Not modelled

`epoll_pwait`/`epoll_pwait2` (a sigmask: signals are not modelled);
`EPIOCSPARAMS`/`EPIOCGPARAMS`; sockets as targets (`napi_id`, busy poll);
pollable fixture files other than `/dev/null`; `POLLFREE` (signalfd, aio);
`EPOLLWAKEUP` with `CONFIG_PM_SLEEP` (off: the bit is cleared, which is
modelled); FIFOs. Each is `unsupported` at its decision.

### 9.3 Modelled but unexercised, and said so

- the `ovflist` (:1466-1471, :925-941): populated only by a callback that
  runs while the same set is being scanned (`ep_is_scanning` is true only
  between `ep_start_scan` and `ep_done_scan` of the same task), which
  needs a second CPU or thread. The scout counted it as substance; in this
  domain it is data of the right shape with its arm marked `invariant`.
  Tier 2's waker thread reaches it.
- `EPOLLEXCLUSIVE` ending a wake walk: needs a sleeper on `ep->wq` (tier 2).
- `-EFAULT` from `epoll_put_uevent`: the guest's buffer is valid.
- the seqcount retry (:581): false with one task.
- `-EPERM` for a target without `poll` (:2498) [AGENT, coordinator
  2026-10-12]: every producer the contract has is pollable, and widening it
  for one arm does not pay; the arm is modelled, its trace dropped. The
  same holds for `vfs_poll`'s `DEFAULT_POLLMASK` arm (poll.h:90).
- `ep_attach_file`'s race arm (:1729), a NULL `f_ep` under the lock with no
  head: `invariant`.

## 10. Risks

1. **The kind-308 record is a kernel change** (record-only). It costs a
   rebuild of both profiles and a new identity, and lands only with the
   merge signoff. Without it, tier 1 shrinks to sets of at most one item,
   which loses the release walks and nesting: not proposed.
2. **The wait-queue service touches every pipe and eventfd wake site.** The
   regression claim (section 8) is the guard; the service with empty queues
   is a no-op by construction.
3. **The warm-up is a fixture fact the mirror depends on** (3.5). If the
   guest's fixture step is skipped or reordered, the first epoll trace of a
   chunk fails the check at :2552 with an unexpected full-check arm: loud,
   and the fixture row's `max_user_watches` value from the same step shows
   whether the step ran.
4. **The function list grows by about 55 functions** across five files; the
   first check runs will surface unlisted helpers (`ep_item_from_wait`,
   `ep_pm_stay_awake`, `__pm_relax` with `CONFIG_PM` off, `noop_llseek`),
   which are inlined or branch-free and go in `branch_free_functions`.
5. **Observation width**: 16 events × 12 bytes exceed the 64-byte head;
   the digest covers the rest, as for reads.

## 11. Execution plan

| Step | Stream | Work | WU |
| --- | --- | --- | --- |
| 0 | coordinator | Measurement on the current oracle: three probe traces with `fs/eventpoll.c` and `wait.c` listed; the covered function set; confirmation that the first ADD of a boot covers `reverse_path_check` and later ones do not (3.5); confirmation that a close-and-create puts a file address out of allocation order (3.2, section 7). | 0.02 |
| 1 | coordinator | The interface commit: opcodes 27-29, `AllocSite` and `HiddenSite` ids (a block 190-199), the `FEp`, `PrivateData.eventpoll`, `FopsId.eventpoll`, `WaitQueue` and `Eventpoll` types, the `Env.lean` warm-up rule. | 0.03 |
| 2 | Q | `Wait.lean`, `Poll.lean`; the pipe and eventfd wake sites as calls, `pipe_resize_ring`'s included; the pipe and eventfd `poll` functions; the regression claim on the existing corpora. | 0.1 |
| 3 | R | The kind-308 hook in `gen-choice-stream.py`; the kernel rebuild; the guest's three operations and its fixture step (the warm-up, the `max_user_watches` read); the trace contract; the domain file with the exclusions; the one-off record mutant. | 0.12 |
| 4 | S | `Eventpoll.lean` with `listFile`/`unlistFile`, the seqcount, the two release walks, the live reverse-path arm; `dispatch`; the observation; depends on Q and the interface. | 0.28 |
| 5 | T | `epoll-corpus.py` (about 50 traces, the limit and diamond traces included), the generator profile, the claim point: full check on the new oracle, controls, sentinels, then one signoff. | 0.1 |

About 0.65 WU in all: the audit's corrections add state, a fixture step
and four traces (C1, C3, C4, C6, C7) and remove the counter modelling
(C2). Q and R run in parallel after step 1; S starts when Q's regression
claim passes; T overlaps S's second half. Tier 2 is a separate design note
once the sleep record exists.

## 12. File ownership

| Stream | Files |
| --- | --- |
| Q | `Leanux/FS/Wait.lean`, `Leanux/FS/Poll.lean` (new); the wake and poll sites in `Leanux/FS/Pipe.lean`, `Leanux/FS/EventfdOps.lean` |
| R | `kernel/patches/gen-choice-stream.py`, `kernel/identity-*.txt`, `harness/guest.c`, `harness/trace.py`, `harness/linux.py`, `contracts/trace-v1.md`, `correspondence/kcov.json`, `harness/steer.py` |
| S | `Leanux/FS/Eventpoll.lean` (new), `Leanux/FS/Syscalls.lean`, `Leanux/FS/FileTable.lean` (`fputFinal`), `Leanux/Runner.lean` (the observation) |
| T | `scripts/epoll-corpus.py`, `corpus/epoll/`, `evaluator/generate.py`, `scripts/pipes-mutants.py` (the one-off, deleted after the claim point) |
| coordinator | `Leanux/Kernel/Defs.lean` (the interface commit), `Leanux/Env.lean` (the warm-up rule), `docs/decisions.md` |

## 13. Decisions

**The user's, at the merge:** the kind-308 address record (3.2) is a
record-only oracle change, approved as a class under "Oracle kernel
changes"; it needs no advance ruling and is presented at the claim point's
signoff with the new kernel identity and patch hash. Whether epoll is the
next target at all is the scout's ranking, already before the user.

**Tactical, decided as recommended under the user's 2026-10-12 delegation
and recorded as [AGENT] in `docs/decisions.md`:** tier 1 is timeout 0 with
blocking waits `unsupported` until a sleep record exists (9.1); the rbtree
is an ordered-map cut by listing `ep_find` and `ep_rbtree_insert` as
decision-free functions and naming the cut in code (3.2); nested epoll is
in tier 1, both arms of the limits (2.7); the fixture warm-up and the
relative `loop_check_gen` (3.5); the wire mapping with opcodes 27-29
proposed for the coordinator to allocate (6); the `max_user_watches`
fixture check (3.4); the kind-308 one-off as the only new mutant (7).

## 14. Revision v2 — audit response [AGENT, fork of the coordinator 2026-10-12]

Every finding of section 15 was re-verified at the source before adoption;
the "Verified" column says what was read. Dispositions, with the section
that carries the change:

| Finding | Verified (`.deps/linux` 6.12.110) | Disposition |
| --- | --- | --- |
| C1 `loop_check_gen` boot-global; first ADD per boot takes the full check | :394 `static u64 loop_check_gen = 0`; :2552 the `ep->gen == loop_check_gen` disjunct; :2558 and :2615 the two increments; :2302, :2344 the in-check tests; `check.py:58` `CHUNK = 100`; no epoll call in `harness/guest.c` | Adopted: 3.5 (new), 2.2, 4.1 (`loopCheckGen := 2`, relative), 4.4 (three exclusions, :2552 arm `invariant`), 5 (the warm-up rule), 6 (the fixture step), 11 (step 0 confirms it), risk 3 |
| C2 no `CONFIG_SMP` | config: `CONFIG_NR_CPUS=1`, no `CONFIG_SMP`; `lib/Makefile:201`; `percpu_counter.h:171-179`; `ep_alloc_epitem` :1759-1760 | Adopted: 3.4 rewritten (plain `Nat`, two `branchCmp`s, no exclusion), `lib/percpu_counter.c` dropped from 6, risk 3 and step 0's measurement replaced |
| C3 `ep_events_available` reads `ep->seq` | :576-582; `ep_is_scanning` :539-542; `ep_start_scan` :905, :910; `ep_done_scan` :942, :952; callback :1457, :1466-1471, :1472-1475; `epi_on_ovflist` :557-560 | Adopted: 2.5 and 2.6 corrected, `seq` in 4.1, the retry in 4.4 (`invariant`) and 9.3, `seqlock.h` listed in 6 |
| C4 reverse-path limits reachable within 32 fds | `reverse_path_check_proc` :1624-1643 (recursion into `epi->ep->refs`, count at an unwatched top), `path_count_inc` :1605-1614, `path_limits` :1602, :1629; the depth-4 construction re-derived: 2·2·2·2·1 = 16 chains > 10 at V1's second ADD, nine sets, loop check depth 3 + 1 + 0 | Adopted: 2.7 rewritten, 4.5, two limit traces and a diamond trace in 7, 9.3 item removed, estimate |
| C5 eventfd wake lines | `fs/eventfd.c:198` `eventfd_ctx_remove_wait_queue` (holds :207); :237-238 the read-side wake; :273-274 the write-side; :56-79 `eventfd_signal_mask` (wake :76) | Adopted: 2.5 corrected; :56-79 and :198-211 stated outside the domain |
| C6 `tfile_check_list` holds a file reference | `list_file` :425-444 (:430, :438); `unlist_file` :446-462 (:451, :454, :460, :461); `ep_item_poll` :1237 `fput`; `ep_remove_file` :1037 `v->next`; `ep_attach_file` :1729-1731, :1739 | Adopted: 2.2, 2.3, 2.4, 4.1 (the list carries the reference), 4.3 (`unlistFile`), 4.4 |
| C7 wake sites missed | `fs/pipe.c:1327` in `pipe_resize_ring` (:1266), via `F_SETPIPE_SZ` :1409 → :1371; :734 `!readers != !writers`; :381 before :390, :577 before :579; `Pipe.lean:296`, :561 | Adopted: 2.5 (resize site, release condition, tier-2 sites), 1, 7 (two traces), step 2 |
| C8 allocation-site lines | :1764 (`epi_cache`; :1765-1768 the arm), :1550 (`pwq_cache`; :1547 the `!epi` test), :1722 (`ephead_cache`; :1723 the test), :1331 | Adopted: 3.1, 2.3 |
| C9 line and wording slips | `ep_timeout_to_timespec` :2104-2123 (returns :2111-2115 for 0); `do_epoll_ctl` :2479-2619; `ep_insert` :1827-1904; `ep_clear_and_put` :1102-1141; `ep_send_events` :2058-2102; :1855, :1927-1931; :957; :1068; :1120, :1135; `check.py:306` | Adopted throughout 2; the `EPOLLWAKEUP` and :957 decisions in 4.4; :1320 as a refcount compare; the `cond_resched`s through the resched rule. Also found while re-reading: `do_epoll_create` ends :2439, `ep_modify` ends :1980 |
| M1 two whole-tree walks | :1116-1121, :1131-1136, :1081 | Adopted: 2.8, 3.2, 4.3 |
| M2 the walk over a snapshot | `wait.c:85` `list_for_each_entry_safe_from` | Adopted: 4.2 (snapshot asserted as an `invariant` after the walk) |
| M3 fields the C reads | :612 `busy_poll_usecs`; :1440, :1885 | Adopted: 4.1 (`seq`, `busyPollUsecs`), 2.3, 4.4 |
| E1 `cut_functions` is a new rule | `check.py:743-756`, :711-725, :251 | Adopted: no new key; the cut is listing plus naming in code (3.2, 6); decision 3 withdrawn from the user's list |
| E2 the wait-order sentinel | AGENTS.md "Gates and speedbumps" | Adopted: dropped; the trace kept (7, 8) |
| E3 the one-off's subset | — (a corpus matter) | Adopted: `close_three_recycled` (7), confirmed by step 0 |
| E4 the fixture check is required | :1759 | Adopted: 3.4, 6 (the value in the fixture row, the warm-up in the same step) |
| S1 estimate | — | Adopted: 11 (about 0.65 WU), 12 (`Env.lean` to the coordinator) |
| S2 tier 2's `WaitFunc` | `fs/eventfd.c:230`, :265; `fs/pipe.c:390`, :579; :2232-2252 | Adopted: 9.1 (`taskWaiter` as an added constructor) |
| S3 the ovflist | :539-542 | Holds as written; 9.3 says why |
| D1, D2 whose decisions | — | Adopted: 13 rewritten; the user's decision is the record at the merge; the rest tactical, recorded [AGENT] |

Per section, what v2 verified and changed:

- **2 (all of 2.1-2.9):** every range re-read; corrections in 2.1 (end
  line), 2.2 (`loop_check_gen`, `list_file`/`unlist_file`, end line), 2.3
  (allocation lines, `EPOLLWAKEUP`, `ep_set_busy_poll_napi_id`, the `!epi`
  test), 2.4 (end line, `EPOLLWAKEUP`, :1037, :1068), 2.5 (callback lines,
  `ep_poll_safewake` as configured, the pipe and eventfd sites), 2.6
  (`ep_events_available`, `ep_done_scan` lines, :957), 2.7 (the limits
  reachable, the `gen` tests), 2.8 (two walks, `cond_resched`, :1320).
- **3:** 3.1 lines; 3.2 the cut without a checker rule; 3.4 without the
  per-cpu counter; 3.5 new.
- **4:** state, functions and decisions updated for C1, C3, C6, C9, M1-M3.
- **5, 6:** the warm-up rule and the fixture step; the file and exclusion
  lists; no `cut_functions`.
- **7, 8:** traces added (limits, diamond, resize, recycled close); the
  sentinel dropped; the one-off's subset named.
- **9-13:** tier 2's `WaitFunc`, risks renumbered, estimate about 0.65 WU,
  decisions reduced to the one that is the user's.

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

## 16. Stream S: the mirror as built [AGENT, stream S 2026-10-12]

`Leanux/FS/Eventpoll.lean` (new), `Leanux/FS/Fput.lean` (new, 4.6), the
callback group in `Wait.lean` (4.2), `ep_ptable_queue_proc` in `Poll.lean`,
the state in `Defs.lean`, 176 decisions in `Decision.lean` (46 with operands), the three
operations in `Syscalls.lean` and `Runner.lean` (an `epoll_wait`'s events
through the read channel: `bytes` and `digest` over `12·ret` bytes), the
fixture constants in `Env.lean` (section 5), and in `correspondence/kcov.json`
the file, 25 functions, two branch-free helpers and four operand exclusions.

Deviations from sections 2-6, each verified against `.deps/linux`:

1. **Line numbering.** The check reads statement and span lines from the
   pristine tree while the kernel's DWARF is the built source's
   (`-fdebug-prefix-map`), so every patch of an anchored file keeps its line
   count: none of the existing hunks changes one. Stream R's kind-308 hook
   adds an include at line 43 and a call line at 1587, shifting
   `fs/eventpoll.c` by one and then two. The mirror's table uses pristine
   numbers (as the check requires) and the site table names the hook at
   :1585; the hook must be made line-preserving before the claim point: no
   include (an `extern` declaration on the call's line) and the call on the
   line of `rb_insert_color_cached` (:1585), then one more oracle build.
   Until then a check on the e1 oracle attributes the file's points one or
   two lines off.
2. **The cut functions are inlined.** `ep_find` and `ep_rbtree_insert` have
   no symbol (both inlined into `do_epoll_ctl` and `ep_register_epitem`),
   so they cannot be listed in `functions` (the check fails on a listed
   function with no symbol); the cut is the absence of decisions inside
   them, named in the code. `percpu_counter_compare` and
   `do___read_seqcount_retry` own no instrumentation point of their own and
   are `branch_free_functions`.
3. **Decisions added beyond section 2:** `epoll_mutex_lock`'s `nonblock`
   test and the three `error` tests of its callers; `ep_op_has_event` at
   its three callers; the `switch (op)` as three case decisions; the
   `max()` comparisons of the two loop-check walks; `ep_busy_loop_on`'s two
   terms; `free_ephead`'s test; the scoped `__free(fput)` of `ep_remove`;
   `epoll_put_uevent`'s two put tests; `WARN_ON_ONCE`'s tests. Operands are
   declared for the scalar compares the mirror holds (masks, counts, depths,
   `maxevents`, `res`, the seqcount) and not for pointer tests, nor for the
   compares of `op`, whose `==` tests and switch may share one comparison
   in the built code; stream T's first run decides whether they can be
   declared.
4. **Allocation sites** take ids 192-195 of epoll's block (A's 70-99 has
   two ids left before D3's 100); `harness/steer.py ALLOC_SITES` does not
   name them yet, which stream T's steered traces need.
5. **The evaluator:** `address` (and seccomp's `program`) joins the site
   kinds `load_hidden_sites` accepts; an operand exclusion may be declared
   at several call sites of one decision (`root_user.__count` at
   `alloc_pipe_info` and at `ep_alloc`).
6. **Unexercised arms** are listed in 9.3; `ep_poll`'s loop runs once (a
   second iteration needs a sleep or a busy loop) and `eventpoll_release`
   runs on an epoll file too (its `refs` list, the outer items).

