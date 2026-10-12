#!/usr/bin/env python3
"""Writes the epoll tier-1 corpus into corpus/epoll (docs/2026-10-12-epoll-design.md
section 7, one trace per target), in the pipes corpus's style.

Each trace's comment says what Linux 6.12.110 does, with the fs/eventpoll.c
lines (fs/eventfd.c, fs/pipe.c where named) that decide it; the check compares
the mirror against the real kernel, so a comment is a statement of intent, not
an oracle. The output is deterministic: rerunning this script reproduces the
committed files (`--check` verifies that without writing).

Conventions: fds 0-7 are the guest's fixture files, so the first descriptor a
trace allocates is 8 (rlimit_nofile 32 unless stated). Every eventfd and pipe
is non-blocking and every wait has timeout 0 (tier 1), so no operation sleeps.
An `epoll_wait`'s observation is its events through the read channel: the
first 64 bytes of the packed 12-byte `epoll_event` array and the BLAKE2s digest
of all of them, so the order of returned events is checked, not just the count.
`data` is the u64 the kernel copies back, so each item's identity is visible
in the events. Not here: the four steered allocation failures (section 7),
which wait for the AllocSite ids of the interface commit and the mirror's
sites (stream T).
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness.trace import validate_trace  # noqa: E402

OUT = ROOT / "corpus" / "epoll"

# include/uapi/linux/eventpoll.h
EPOLLIN, EPOLLPRI, EPOLLOUT, EPOLLERR, EPOLLHUP = 0x1, 0x2, 0x4, 0x8, 0x10
EPOLLRDNORM, EPOLLWRNORM, EPOLLRDHUP = 0x40, 0x100, 0x2000
EPOLLEXCLUSIVE, EPOLLWAKEUP, EPOLLONESHOT, EPOLLET = 1 << 28, 1 << 29, 1 << 30, 1 << 31
EPOLL_CLOEXEC = 0o2000000
ADD, DEL, MOD = 1, 2, 3
NB = 0o4000                 # O_NONBLOCK = EFD_NONBLOCK
EFD_SEMAPHORE = 1
PIPE_DEFAULT = 16 * 4096    # fs/pipe.c PIPE_DEF_BUFFERS pages
U64_MAX_COUNT = 2**64 - 2   # eventfd's largest count (ULLONG_MAX - 1)


def R(i):
    return {"pipe": i, "end": 0}


def W(i):
    return {"pipe": i, "end": 1}


def ref(i):
    return {"ref": i}


def lit(n):
    return {"literal": n}


def epoll_create1(flags=0):
    return {"op": "epoll_create1", "flags": flags}


def ctl(epfd, cmd, fd, events=EPOLLIN, data=0):
    return {"op": "epoll_ctl", "epfd": epfd, "cmd": cmd, "fd": fd, "events": events, "data": str(data)}


def add(epfd, fd, events=EPOLLIN, data=0):
    return ctl(epfd, ADD, fd, events, data)


def wait(epfd, maxevents=16):
    return {"op": "epoll_wait", "epfd": epfd, "maxevents": maxevents, "timeout": 0}


def eventfd2(init=0, flags=NB):
    return {"op": "eventfd2", "init": init, "flags": flags}


def pipe2(flags=NB):
    return {"op": "pipe2", "flags": flags}


def write(fd, count, value=1):
    return {"op": "write", "fd": fd, "count": count, "value": str(value)}


def read(fd, count=8):
    return {"op": "read", "fd": fd, "count": count}


def fcntl(fd, cmd, arg=0):
    return {"op": "fcntl", "fd": fd, "cmd": cmd, "arg": arg}


def close(fd):
    return {"op": "close", "fd": fd}


def dup(fd):
    return {"op": "dup", "fd": fd}


def dup3(fd, newfd, flags=0):
    return {"op": "dup3", "fd": fd, "newfd": newfd, "flags": flags}


TRACES = {}


def trace(name, ops, **extra):
    TRACES[name] = dict(version=1, id=name, ops=ops, **extra)


# ---- create (2.1) ---------------------------------------------------------

# do_epoll_create (:2398-2439): flags outside EPOLL_CLOEXEC are -EINVAL
# (:2408) before anything is allocated; EPOLL_CLOEXEC lands on the descriptor
# (get_unused_fd_flags, :2416), visible to F_GETFD; the anon inode file's
# f_flags are O_RDWR (:2421). 2^31 is a negative int: outside the mask.
trace("e_create_flags", [
    epoll_create1(0),                          # 0: 8
    epoll_create1(EPOLL_CLOEXEC),              # 1: 9
    fcntl(ref(0), "F_GETFD"),                  # 2: 0
    fcntl(ref(1), "F_GETFD"),                  # 3: FD_CLOEXEC
    fcntl(ref(0), "F_GETFL"),                  # 4: O_RDWR
    epoll_create1(1),                          # 5: -EINVAL
    epoll_create1(2 ** 31),                    # 6: -EINVAL
    epoll_create1(EPOLL_CLOEXEC | 2),          # 7: -EINVAL
    close(ref(0)),
    close(ref(1)),
    epoll_create1(0),                          # 10: 8 again
])

# A dup'd set is the same file: an ADD through the duplicate and a second
# ADD of the same (file, fd) pair through the original find the item
# (ep_find, :1356-1378) and fail with -EEXIST (:2586). Closing the duplicate
# keeps the set alive (f_count): the next wait still delivers.
trace("e_create_dup", [
    epoll_create1(),                           # 0: 8
    dup(ref(0)),                               # 1: 9
    eventfd2(),                                # 2: 10
    add(ref(1), ref(2), EPOLLIN, 1),           # 3: 0
    add(ref(0), ref(2), EPOLLIN, 2),           # 4: -EEXIST
    wait(ref(1)),                              # 5: 0 (the counter is zero)
    write(ref(2), 8, 1),                       # 6: 8 (eventfd_write's wake, fs/eventfd.c:274)
    wait(ref(0)),                              # 7: 1 [IN, 1]
    close(ref(1)),                             # 8: 0
    wait(ref(0)),                              # 9: 1 (level-triggered)
    close(ref(0)),
    close(ref(2)),
])

# EMFILE after the set is allocated: ep_alloc succeeds, get_unused_fd_flags
# fails (:2416-2419), ep_clear_and_put frees the empty set (:2437). The
# descriptor is not consumed.
trace("e_create_emfile", [
    epoll_create1(),                           # 0: 8
    epoll_create1(),                           # 1: -EMFILE
    eventfd2(),                                # 2: -EMFILE
    close(ref(0)),
    epoll_create1(),                           # 4: 8
], rlimit_nofile=9)

# ---- ctl errors (2.2) -----------------------------------------------------

# fdget(epfd) fails first (:2490), then fdget(fd) (:2495); a negative epfd
# and a closed one are both -EBADF.
trace("e_ctl_ebadf", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    ctl(lit(20), ADD, ref(1)),                 # 2: -EBADF
    ctl(lit(-1), ADD, ref(1)),                 # 3: -EBADF
    ctl(ref(0), ADD, lit(21)),                 # 4: -EBADF
    ctl(ref(0), DEL, lit(21)),                 # 5: -EBADF
    close(ref(1)),
    ctl(ref(0), ADD, ref(1)),                  # 7: -EBADF (closed target)
    close(ref(0)),
])

# -EINVAL (:2510): the set as its own target (f == tf, through the original
# and through a dup), an eventfd or a pipe end as the set
# (!is_file_epoll(f)); an unknown operation number falls through the switch
# (:2579, :2610) after every earlier check, so 0 and 7 are -EINVAL with the
# item untouched (the following ADD succeeds).
trace("e_ctl_einval", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    pipe2(),                                   # 2: 10, 11
    dup(ref(0)),                               # 3: 12
    ctl(ref(0), ADD, ref(0)),                  # 4: -EINVAL
    ctl(ref(0), ADD, ref(3)),                  # 5: -EINVAL (the same file)
    ctl(ref(1), ADD, ref(0)),                  # 6: -EINVAL (not an epoll file)
    ctl(R(2), ADD, ref(1)),                    # 7: -EINVAL
    ctl(ref(0), 7, ref(1)),                    # 8: -EINVAL (unknown op)
    ctl(ref(0), 0, ref(1)),                    # 9: -EINVAL
    ctl(ref(0), ADD, ref(1)),                  # 10: 0
    ctl(ref(0), 7, ref(1)),                    # 11: -EINVAL (present, unknown op)
    close(ref(0)),
])

# The switch (:2581-2609): ADD of a present pair is -EEXIST, DEL and MOD of an
# absent one -ENOENT; a re-ADD after DEL is a new item. DEL ignores the
# event (ep_op_has_event, :2461: no copy, so the values are never read).
trace("e_ctl_eexist_enoent", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    ctl(ref(0), MOD, ref(1), EPOLLIN, 5),      # 2: -ENOENT
    ctl(ref(0), DEL, ref(1)),                  # 3: -ENOENT
    add(ref(0), ref(1), EPOLLIN, 1),           # 4: 0
    add(ref(0), ref(1), EPOLLOUT, 2),          # 5: -EEXIST
    ctl(ref(0), DEL, ref(1), 2 ** 32 - 1, 2 ** 64 - 1),   # 6: 0 (the event is not read)
    ctl(ref(0), DEL, ref(1)),                  # 7: -ENOENT
    add(ref(0), ref(1), EPOLLIN, 3),           # 8: 0
    write(ref(1), 8, 1),
    wait(ref(0)),                              # 10: 1 [IN, 3]
    close(ref(1)),
    close(ref(0)),
])

# EPOLLEXCLUSIVE (:2515-2523): refused on MOD, on an epoll target and with
# bits outside EPOLLEXCLUSIVE_OK_BITS (:216); accepted with every OK bit. A
# present exclusive item refuses MOD without the bit too (:2602-2604).
trace("e_ctl_exclusive", [
    epoll_create1(),                           # 0: 8 (A)
    epoll_create1(),                           # 1: 9 (B)
    eventfd2(),                                # 2: 10
    eventfd2(),                                # 3: 11
    add(ref(0), ref(2), EPOLLEXCLUSIVE | EPOLLIN, 1),                 # 4: 0
    ctl(ref(0), MOD, ref(2), EPOLLEXCLUSIVE | EPOLLIN, 1),            # 5: -EINVAL (MOD)
    ctl(ref(0), MOD, ref(2), EPOLLIN, 1),                             # 6: -EINVAL (present and exclusive)
    add(ref(0), ref(1), EPOLLEXCLUSIVE | EPOLLIN),                    # 7: -EINVAL (epoll target)
    add(ref(0), ref(3), EPOLLEXCLUSIVE | EPOLLIN | EPOLLONESHOT),     # 8: -EINVAL (ONESHOT is not an OK bit)
    add(ref(0), ref(3), EPOLLEXCLUSIVE | EPOLLIN | EPOLLRDNORM),      # 9: -EINVAL (RDNORM is not)
    add(ref(0), ref(3), EPOLLEXCLUSIVE | EPOLLIN | EPOLLOUT | EPOLLERR | EPOLLHUP | EPOLLET | EPOLLWAKEUP, 2),  # 10: 0
    write(ref(3), 8, 1),
    wait(ref(0)),                              # 12: 1 [IN|OUT, 2] (10 is ready too: OUT)
    close(ref(0)),
    close(ref(1)),
])

# EPOLLWAKEUP is cleared without CONFIG_PM_SLEEP (:2461-2464) on ADD and
# MOD; the delivered events never carry it.
trace("e_ctl_wakeup_masked", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    add(ref(0), ref(1), EPOLLIN | EPOLLWAKEUP, 7),       # 2: 0
    write(ref(1), 8, 1),
    wait(ref(0)),                              # 4: 1 [IN, 7]
    ctl(ref(0), MOD, ref(1), EPOLLIN | EPOLLOUT | EPOLLWAKEUP, 8),   # 5: 0
    wait(ref(0)),                              # 6: 1 [IN|OUT, 8]
    close(ref(0)),
])

# epoll_wait's own errors (do_epoll_wait, :2642-2682): -EBADF for a closed
# epfd, -EINVAL for a file that is not an epoll set.
trace("e_wait_errors", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    pipe2(),                                   # 2: 10, 11
    wait(lit(20)),                             # 3: -EBADF
    wait(ref(1)),                              # 4: -EINVAL
    wait(R(2)),                                # 5: -EINVAL
    wait(ref(0), 1),                           # 6: 0
    close(ref(0)),
    wait(ref(0)),                              # 8: -EBADF
])

# ---- loops and nesting (2.7) ---------------------------------------------

# A 2-cycle: B into A succeeds; A into B walks A's tree (ep_loop_check,
# :2364; ep_loop_check_proc, :2296) and meets B, the inserting set
# (:2311-2312): EP_MAX_NESTS + 1, -ELOOP (:2562-2563).
trace("e_nest_eloop_cycle", [
    epoll_create1(),                           # 0: 8 (A)
    epoll_create1(),                           # 1: 9 (B)
    add(ref(0), ref(1)),                       # 2: 0
    add(ref(1), ref(0)),                       # 3: -ELOOP
    eventfd2(),                                # 4: 10
    add(ref(1), ref(4), EPOLLIN, 4),           # 5: 0
    write(ref(4), 8, 1),
    wait(ref(0)),                              # 7: 1 [IN, 0] (B is ready: its item's data)
    close(ref(0)),
    close(ref(1)),
])

# Five sets chained bottom-up: the last ADD (S1 into S0) finds depth 3 under
# S1 and upward depth 0 above S0 (ep_get_upwards_depth_proc, :2339):
# 3 + 1 + 0 = EP_MAX_NESTS, allowed (:2381). A sixth set over S0 finds depth
# 4: 4 + 1 + 0 > EP_MAX_NESTS, -ELOOP.
trace("e_nest_chain", [
    epoll_create1(),                           # 0: 8 (S0)
    epoll_create1(),                           # 1: 9 (S1)
    epoll_create1(),                           # 2: 10 (S2)
    epoll_create1(),                           # 3: 11 (S3)
    epoll_create1(),                           # 4: 12 (S4)
    add(ref(3), ref(4)),                       # 5: 0
    add(ref(2), ref(3)),                       # 6: 0
    add(ref(1), ref(2)),                       # 7: 0
    add(ref(0), ref(1)),                       # 8: 0 (depth 3 + 1 + 0)
    epoll_create1(),                           # 9: 13 (S)
    add(ref(9), ref(0)),                       # 10: -ELOOP (depth 4 + 1 + 0)
    eventfd2(),                                # 11: 14
    add(ref(4), ref(11), EPOLLIN, 4),          # 12: 0 (ready chain: S4 .. S0)
    write(ref(11), 8, 1),                      # 13: the callback climbs four poll_wait heads
    wait(ref(0)),                              # 14: 1 [IN, 0]
    close(ref(0)),
])

# The same chain built top-down: each ADD finds depth 0 below and the
# upward depth of the inserting set; the fifth (S5 into S4, upward 4) is
# 0 + 1 + 4 > EP_MAX_NESTS, -ELOOP.
trace("e_nest_chain_topdown", [
    epoll_create1(),                           # 0: 8 (S0)
    epoll_create1(),                           # 1: 9
    epoll_create1(),                           # 2: 10
    epoll_create1(),                           # 3: 11
    epoll_create1(),                           # 4: 12
    epoll_create1(),                           # 5: 13 (S5)
    add(ref(0), ref(1)),                       # 6: 0 (0 + 1 + 0)
    add(ref(1), ref(2)),                       # 7: 0 (0 + 1 + 1)
    add(ref(2), ref(3)),                       # 8: 0 (0 + 1 + 2)
    add(ref(3), ref(4)),                       # 9: 0 (0 + 1 + 3)
    add(ref(4), ref(5)),                       # 10: -ELOOP (0 + 1 + 4)
    close(ref(0)),
])

# The design's diamond: A and B watch E, C watches A and B. Each ADD into C
# lists E (list_file, :2327) and reverse_path_check (:1655) counts the chains
# above E: through A (watched by C once the first ADD is in: depth 1) and
# B (no watcher yet: depth 0), well inside path_limits. A write to E reaches
# C twice, through A and through B (ep_poll_safewake, :1511), in E's queue
# order: B registered last and sits at the head (add_wait_queue), so C's
# wait returns B's item first.
trace("e_nest_diamond", [
    epoll_create1(),                           # 0: 8 (A)
    epoll_create1(),                           # 1: 9 (B)
    epoll_create1(),                           # 2: 10 (C)
    eventfd2(),                                # 3: 11 (E)
    add(ref(0), ref(3), EPOLLIN, 1),           # 4: 0
    add(ref(1), ref(3), EPOLLIN, 2),           # 5: 0
    add(ref(2), ref(0), EPOLLIN, 10),          # 6: 0
    add(ref(2), ref(1), EPOLLIN, 20),          # 7: 0
    write(ref(3), 8, 1),
    wait(ref(2)),                              # 9: 2 [IN, 20], [IN, 10]
    wait(ref(0)),                              # 10: 1 [IN, 1]
    wait(ref(2)),                              # 11: 2 (level-triggered through the inner sets)
    read(ref(3)),
    wait(ref(2)),                              # 13: 0 (the inner items are polled and dropped)
    close(ref(2)),
])

# A set reached twice in one downward walk: X watches A and B, both watch S;
# D into X visits S through A (marked, :2306) and again through B, where
# :2302 returns the cached depth. Depth 2 + 1 + 0: allowed.
trace("e_nest_diamond_down", [
    epoll_create1(),                           # 0: 8 (S)
    epoll_create1(),                           # 1: 9 (A)
    epoll_create1(),                           # 2: 10 (B)
    epoll_create1(),                           # 3: 11 (X)
    epoll_create1(),                           # 4: 12 (D)
    add(ref(1), ref(0)),                       # 5: 0
    add(ref(2), ref(0)),                       # 6: 0
    add(ref(3), ref(1)),                       # 7: 0
    add(ref(3), ref(2)),                       # 8: 0
    add(ref(4), ref(3)),                       # 9: 0 (S cached on the second visit)
    close(ref(4)),
])

# A set reached twice in the upward walk: T watches A and B, both watch Y;
# Z into Y climbs Y's refs (ep_get_upwards_depth_proc, :2339) to T through
# A (marked) and through B (:2344 cached). Depth 0 + 1 + 2: allowed.
trace("e_nest_diamond_up", [
    epoll_create1(),                           # 0: 8 (T)
    epoll_create1(),                           # 1: 9 (A)
    epoll_create1(),                           # 2: 10 (B)
    epoll_create1(),                           # 3: 11 (Y)
    epoll_create1(),                           # 4: 12 (Z)
    add(ref(0), ref(1)),                       # 5: 0
    add(ref(0), ref(2)),                       # 6: 0
    add(ref(1), ref(3)),                       # 7: 0
    add(ref(2), ref(3)),                       # 8: 0
    add(ref(3), ref(4)),                       # 9: 0 (T cached on the second climb)
    close(ref(0)),
])

# The reverse-path limit at depth 4 (2.7; path_limits {1000, 500, 100, 50,
# 10}, :1602): five tiers of two sets over one eventfd, fully connected.
# With V1 over U1 there are 8 chains at depth 4; V1's ADD of U2 makes 16,
# and the eleventh fails path_count_inc (:1611): reverse_path_check returns
# -1, ep_insert removes the item and returns -EINVAL (:1850-1852). The loop
# check passes at every step (depth at most 3, plus 1, plus 0 upward).
_rp4 = [eventfd2()] + [epoll_create1() for _ in range(9)]   # 0: E (8); 1-2: S1, S2; 3-4: O1, O2; 5-6: T1, T2; 7-8: U1, U2; 9: V1
_rp4 += [add(ref(s), ref(0), EPOLLIN, s) for s in (1, 2)]
_rp4 += [add(ref(o), ref(s)) for o in (3, 4) for s in (1, 2)]
_rp4 += [add(ref(t), ref(o)) for t in (5, 6) for o in (3, 4)]
_rp4 += [add(ref(u), ref(t)) for u in (7, 8) for t in (5, 6)]
_rp4 += [add(ref(9), ref(7)),                  # 24: 0 (8 chains at depth 4)
         add(ref(9), ref(8)),                  # 25: -EINVAL (16 chains at depth 4 > 10)
         ctl(ref(9), DEL, ref(8)),             # 26: -ENOENT (the item was removed)
         write(ref(0), 8, 1),
         wait(ref(9)),                         # 28: 1 [IN, 0] (U1's item)
         close(ref(9))]
trace("e_reverse_depth4", _rp4)

# The limit at depth 2 (100): five S over E, four O over every S, six T over
# every O. T1..T5 complete give 5 * 4 * 5 = 100 chains at depth 2, the limit
# exactly (:1611 is `>`); T6's first ADD makes 105 and fails with -EINVAL.
_rp2 = [eventfd2()] + [epoll_create1() for _ in range(15)]  # 0: E; 1-5: S; 6-9: O; 10-15: T
_rp2 += [add(ref(s), ref(0), EPOLLIN, s) for s in range(1, 6)]
_rp2 += [add(ref(o), ref(s)) for o in range(6, 10) for s in range(1, 6)]
_rp2 += [add(ref(t), ref(o)) for t in range(10, 15) for o in range(6, 10)]
_rp2 += [add(ref(15), ref(6))]                 # 61: -EINVAL (101st chain at depth 2)
trace("e_reverse_depth2", _rp2)

# ---- readiness at insert (2.3) ---------------------------------------------

# ep_insert polls the target with the queue proc (:1800-1803): an empty
# eventfd is not ready (eventfd_poll, fs/eventfd.c:124-150: EPOLLOUT only,
# outside the IN mask), a written one is.
trace("e_ready_eventfd", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    eventfd2(),                                # 2: 10
    write(ref(2), 8, 3),                       # 3: 8
    add(ref(0), ref(1), EPOLLIN, 1),           # 4: 0 (not ready)
    add(ref(0), ref(2), EPOLLIN | EPOLLOUT, 2),    # 5: 0 (ready: IN and OUT)
    wait(ref(0)),                              # 6: 1 [IN|OUT, 2]
    wait(ref(0), 1),                           # 7: 1
    close(ref(0)),
])

# A pipe's ends at insert (pipe_poll, fs/pipe.c:657-705): the read end of an
# empty pipe is not ready, the write end is (EPOLLOUT|EPOLLWRNORM); with 5
# bytes in it the read end is EPOLLIN|EPOLLRDNORM. A full pipe's write end
# is not ready until a read frees a slot (pipe_read's wr_wait wake, :402).
trace("e_ready_pipe", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    pipe2(),                                   # 2: 11, 12
    add(ref(0), R(1), EPOLLIN, 1),             # 3: 0 (empty)
    add(ref(0), W(1), EPOLLOUT, 2),            # 4: 0 (ready)
    wait(ref(0)),                              # 5: 1 [OUT, 2]
    write(W(2), 5),                            # 6: 5
    add(ref(0), R(2), EPOLLIN | EPOLLRDNORM, 3),   # 7: 0 (ready)
    wait(ref(0)),                              # 8: 2 [OUT, 2], [IN|RDNORM, 3]
    close(ref(0)),
])

trace("e_ready_pipe_full", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    write(W(1), PIPE_DEFAULT),                 # 2: 65536 (16 pages: full)
    add(ref(0), W(1), EPOLLOUT, 1),            # 3: 0 (not ready)
    wait(ref(0)),                              # 4: 0
    read(R(1), 4096),                          # 5: 4096 (one slot freed; wr_wait woken with EPOLLOUT|EPOLLWRNORM)
    wait(ref(0)),                              # 6: 1 [OUT, 1]
    close(ref(0)),
])

# ---- the callback (2.5) ---------------------------------------------------

# A write after the insert queues the item through ep_poll_callback (:1429);
# level-triggered, it is returned by every wait until the read empties the
# counter (then dropped at delivery, :2021-2024).
trace("e_cb_write_then_wait", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    add(ref(0), ref(1), EPOLLIN, 1),           # 2: 0
    wait(ref(0)),                              # 3: 0
    write(ref(1), 8, 1),                       # 4: 8
    wait(ref(0)),                              # 5: 1 [IN, 1]
    wait(ref(0)),                              # 6: 1
    wait(ref(0), 1),                           # 7: 1
    read(ref(1)),                              # 8: 8
    wait(ref(0)),                              # 9: 0
    close(ref(0)),
])

# A full eventfd (count ULLONG_MAX - 1) is not writable; the read empties it
# and wakes with EPOLLOUT (fs/eventfd.c:237-238, under waitqueue_active), so
# an OUT watcher sees it.
trace("e_cb_read_gives_out", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    write(ref(1), 8, U64_MAX_COUNT),           # 2: 8
    add(ref(0), ref(1), EPOLLOUT, 1),          # 3: 0 (not ready)
    wait(ref(0)),                              # 4: 0
    write(ref(1), 8, 1),                       # 5: -EAGAIN (does not fit)
    read(ref(1)),                              # 6: 8 (bytes fe ff .. ff)
    wait(ref(0)),                              # 7: 1 [OUT, 1]
    close(ref(0)),
])

# A semaphore eventfd with count 2: each read takes one. The read's wake
# carries EPOLLOUT (fs/eventfd.c:238), outside the item's IN mask, so the
# callback skips it (:1457); the item stays on the ready list from its
# level-triggered re-add until the counter is zero.
trace("e_cb_semaphore", [
    epoll_create1(),                           # 0: 8
    eventfd2(0, NB | EFD_SEMAPHORE),           # 1: 9
    write(ref(1), 8, 2),                       # 2: 8
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0 (ready)
    read(ref(1)),                              # 4: 8 (value 1; count 1)
    wait(ref(0)),                              # 5: 1 [IN, 1]
    read(ref(1)),                              # 6: 8 (count 0)
    wait(ref(0)),                              # 7: 0
    read(ref(1)),                              # 8: -EAGAIN
    close(ref(0)),
])

# EPOLLET: delivered once per wake (no re-add, :2044-2052); a second write
# queues it again.
trace("e_cb_et_once", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    add(ref(0), ref(1), EPOLLIN | EPOLLET, 1),     # 2: 0
    write(ref(1), 8, 1),                       # 3: 8
    wait(ref(0)),                              # 4: 1 [IN, 1]
    wait(ref(0)),                              # 5: 0
    write(ref(1), 8, 1),                       # 6: 8
    wait(ref(0)),                              # 7: 1
    wait(ref(0)),                              # 8: 0
    close(ref(0)),
])

# EPOLLONESHOT: after the delivery only the private bits remain (:2042-2043),
# so the callback skips the item (:1448) and the wait polls nothing; MOD
# re-arms it (ep_modify, :1900-1952: the re-poll at :1937 queues a ready item).
trace("e_cb_oneshot_mod", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    add(ref(0), ref(1), EPOLLIN | EPOLLONESHOT, 1),    # 2: 0
    write(ref(1), 8, 1),                       # 3: 8
    wait(ref(0)),                              # 4: 1 [IN, 1]
    wait(ref(0)),                              # 5: 0
    write(ref(1), 8, 1),                       # 6: 8 (the callback skips a disarmed item)
    wait(ref(0)),                              # 7: 0
    ctl(ref(0), MOD, ref(1), EPOLLIN | EPOLLONESHOT, 2),   # 8: 0 (re-armed, ready)
    wait(ref(0)),                              # 9: 1 [IN, 2]
    wait(ref(0)),                              # 10: 0
    close(ref(0)),
])

# MOD changes the mask and the data: the re-poll in ep_modify keeps a ready
# item queued; an empty mask makes the next delivery drop it; IN|OUT
# restores both bits; the data follows the last MOD.
trace("e_cb_mod_mask", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    write(ref(1), 8, 1),                       # 2: 8
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0
    wait(ref(0)),                              # 4: 1 [IN, 1]
    ctl(ref(0), MOD, ref(1), EPOLLOUT, 2),     # 5: 0
    wait(ref(0)),                              # 6: 1 [OUT, 2]
    ctl(ref(0), MOD, ref(1), 0, 3),            # 7: 0
    wait(ref(0)),                              # 8: 0 (dropped: nothing in the mask)
    ctl(ref(0), MOD, ref(1), EPOLLIN | EPOLLOUT, 4),   # 9: 0 (re-queued)
    wait(ref(0)),                              # 10: 1 [IN|OUT, 4]
    close(ref(0)),
])

# DEL of a ready item unlinks it (ep_remove_safe -> ep_remove, :1065-1100);
# a fresh ADD polls it ready again.
trace("e_cb_del_ready", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    write(ref(1), 8, 1),                       # 2: 8
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0
    wait(ref(0)),                              # 4: 1 [IN, 1]
    ctl(ref(0), DEL, ref(1)),                  # 5: 0
    wait(ref(0)),                              # 6: 0
    add(ref(0), ref(1), EPOLLIN, 2),           # 7: 0
    wait(ref(0)),                              # 8: 1 [IN, 2]
    close(ref(0)),
])

# F_SETPIPE_SZ on a watched full pipe: pipe_resize_ring wakes wr_wait with a
# NULL key (fs/pipe.c:1327), the callback queues the item whatever the key
# (:1457 is skipped for pollflags 0) and the wait polls EPOLLOUT: 16 of 32
# slots used.
trace("e_cb_setpipe_sz", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    write(W(1), PIPE_DEFAULT),                 # 2: 65536
    add(ref(0), W(1), EPOLLOUT, 1),            # 3: 0 (not ready)
    wait(ref(0)),                              # 4: 0
    fcntl(W(1), "F_SETPIPE_SZ", 2 * PIPE_DEFAULT),     # 5: 131072
    wait(ref(0)),                              # 6: 1 [OUT, 1]
    write(W(1), 4096),                         # 7: 4096
    wait(ref(0)),                              # 8: 1 (still room)
    close(ref(0)),
])

# Both ends of one pipe in one set: the write end is ready at insert; a
# write makes the read end ready and the order of the ready list is the
# write end (re-added by the first wait) then the read end (queued by the
# callback); a read drops the read end at the next delivery.
trace("e_cb_pipe_both_ends", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    add(ref(0), R(1), EPOLLIN, 1),             # 2: 0
    add(ref(0), W(1), EPOLLOUT, 2),            # 3: 0 (ready)
    wait(ref(0)),                              # 4: 1 [OUT, 2]
    write(W(1), 3),                            # 5: 3
    wait(ref(0)),                              # 6: 2 [OUT, 2], [IN, 1]
    read(R(1), 3),                             # 7: 3
    wait(ref(0)),                              # 8: 1 [OUT, 2]
    close(ref(0)),
])

# ---- order (2.5, 2.6) -----------------------------------------------------

# One eventfd added twice through a dup: two items on one wait queue head.
# add_wait_queue inserts at the head (kernel/sched/wait.c:17-23), so the
# later-registered entry (the dup's) runs first and its item is queued
# first: the wait returns [dup's, original's].
trace("e_order_dup_twice", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    dup(ref(1)),                               # 2: 10
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0
    add(ref(0), ref(2), EPOLLIN, 2),           # 4: 0
    write(ref(1), 8, 1),                       # 5: 8
    wait(ref(0)),                              # 6: 2 [IN, 2], [IN, 1]
    wait(ref(0), 1),                           # 7: 1 [IN, 2]
    wait(ref(0), 1),                           # 8: 1 [IN, 1] (the leftover first)
    close(ref(0)),
])

# Two sets on one eventfd, one exclusive: the exclusive entry sits at the
# tail (add_wait_queue_exclusive, wait.c:28-36); the walk (:73-97) does not
# stop at a non-exclusive entry, and ep_poll_callback returns 0 for an
# exclusive item with no sleeper (:1514-1515), so both sets queue the event
# whichever was added first.
trace("e_order_two_sets_exclusive", [
    epoll_create1(),                           # 0: 8 (A)
    epoll_create1(),                           # 1: 9 (B)
    eventfd2(),                                # 2: 10
    eventfd2(),                                # 3: 11
    add(ref(0), ref(2), EPOLLEXCLUSIVE | EPOLLIN, 1),  # 4: 0
    add(ref(1), ref(2), EPOLLIN, 2),           # 5: 0
    add(ref(1), ref(3), EPOLLIN, 3),           # 6: 0
    add(ref(0), ref(3), EPOLLEXCLUSIVE | EPOLLIN, 4),  # 7: 0 (exclusive added last)
    write(ref(2), 8, 1),
    write(ref(3), 8, 1),
    wait(ref(0)),                              # 10: 2 [IN, 1], [IN, 4]
    wait(ref(1)),                              # 11: 2 [IN, 2], [IN, 3]
    close(ref(0)),
    close(ref(1)),
])

# maxevents short of the ready count: ep_send_events delivers the first two
# and re-adds them at the tail (:2044-2052); the next wait sees the third
# first, then the first again; a full wait sees the rotated order.
trace("e_order_maxevents_short", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    eventfd2(),                                # 2: 10
    eventfd2(),                                # 3: 11
    write(ref(1), 8, 1),
    write(ref(2), 8, 1),
    write(ref(3), 8, 1),
    add(ref(0), ref(1), EPOLLIN, 1),           # 7: 0 (ready at insert: list order 1, 2, 3)
    add(ref(0), ref(2), EPOLLIN, 2),           # 8: 0
    add(ref(0), ref(3), EPOLLIN, 3),           # 9: 0
    wait(ref(0), 2),                           # 10: 2 [1, 2]
    wait(ref(0), 2),                           # 11: 2 [3, 1]
    wait(ref(0)),                              # 12: 3 [2, 3, 1]
    read(ref(3)),                              # 13: 8
    wait(ref(0), 2),                           # 14: 2 [2, 1] (3 is polled and dropped)
    close(ref(0)),
])

# ---- nesting at run time (2.7) ----------------------------------------------

# Readiness propagates upward: a write to an eventfd in the inner set runs
# the inner's callback, and with the outer registered on the inner's
# poll_wait head, ep_poll_safewake (:815-819) runs the outer's callback with
# key EPOLLIN.
trace("e_nest_propagate", [
    epoll_create1(),                           # 0: 8 (I)
    epoll_create1(),                           # 1: 9 (O)
    eventfd2(),                                # 2: 10
    add(ref(0), ref(2), EPOLLIN, 1),           # 3: 0
    add(ref(1), ref(0), EPOLLIN, 10),          # 4: 0 (not ready)
    wait(ref(1)),                              # 5: 0
    write(ref(2), 8, 1),                       # 6: 8
    wait(ref(1)),                              # 7: 1 [IN, 10]
    wait(ref(0)),                              # 8: 1 [IN, 1]
    read(ref(2)),                              # 9: 8
    wait(ref(1)),                              # 10: 0 (the outer polls the inner: nothing ready)
    close(ref(1)),
    close(ref(0)),
])

# An inner set that is ready when the outer adds it (ep_item_poll at insert
# runs __ep_eventpoll_poll, :1176-1212).
trace("e_nest_ready_at_insert", [
    epoll_create1(),                           # 0: 8 (I)
    epoll_create1(),                           # 1: 9 (O)
    eventfd2(),                                # 2: 10
    write(ref(2), 8, 1),
    add(ref(0), ref(2), EPOLLIN, 1),           # 4: 0 (ready)
    add(ref(1), ref(0), EPOLLIN, 10),          # 5: 0 (ready: the inner has a ready item)
    wait(ref(1)),                              # 6: 1 [IN, 10]
    close(ref(1)),
    close(ref(0)),
])

# The outer's poll of the inner edits the inner's ready list: an item no
# longer ready is unlinked at :1206 by the outer's wait before the inner's
# own wait sees it; the inner's wait then returns only the ready one.
trace("e_nest_outer_prunes", [
    epoll_create1(),                           # 0: 8 (I)
    epoll_create1(),                           # 1: 9 (O)
    eventfd2(),                                # 2: 10
    eventfd2(),                                # 3: 11
    write(ref(2), 8, 1),
    write(ref(3), 8, 1),
    add(ref(0), ref(2), EPOLLIN, 1),           # 6: 0 (ready)
    add(ref(0), ref(3), EPOLLIN, 2),           # 7: 0 (ready)
    add(ref(1), ref(0), EPOLLIN, 10),          # 8: 0 (ready)
    read(ref(2)),                              # 9: 8 (item 1 stays on the inner's list, not ready)
    wait(ref(1)),                              # 10: 1 [IN, 10] (the outer's poll prunes item 1)
    wait(ref(0)),                              # 11: 1 [IN, 2]
    close(ref(1)),
    close(ref(0)),
])

# Closing the inner while watched: its last reference goes through
# eventpoll_release_file (:1287-1325), which removes the outer's item, then
# ep_eventpoll_release clears the inner's own items. The outer's wait finds
# nothing; a DEL names a closed descriptor.
trace("e_nest_close_inner", [
    epoll_create1(),                           # 0: 8 (I)
    epoll_create1(),                           # 1: 9 (O)
    eventfd2(),                                # 2: 10
    write(ref(2), 8, 1),
    add(ref(0), ref(2), EPOLLIN, 1),           # 4: 0
    add(ref(1), ref(0), EPOLLIN, 10),          # 5: 0 (ready)
    wait(ref(1)),                              # 6: 1 [IN, 10]
    close(ref(0)),                             # 7: 0
    wait(ref(1)),                              # 8: 0
    ctl(ref(1), DEL, ref(0)),                  # 9: -EBADF
    close(ref(1)),
])

# ---- release (2.8) --------------------------------------------------------

# Closing a watched eventfd: eventpoll_release_file removes its item (the
# ready-list entry included); the descriptor number is reused by a new
# eventfd, whose ADD is a new item, not -EEXIST.
trace("e_release_eventfd", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    add(ref(0), ref(1), EPOLLIN, 1),           # 2: 0
    write(ref(1), 8, 1),
    wait(ref(0)),                              # 4: 1 [IN, 1]
    close(ref(1)),                             # 5: 0
    wait(ref(0)),                              # 6: 0
    eventfd2(),                                # 7: 9 (reused)
    add(ref(0), ref(7), EPOLLIN, 2),           # 8: 0
    wait(ref(0)),                              # 9: 0
    write(ref(7), 8, 1),
    wait(ref(0)),                              # 11: 1 [IN, 2]
    close(ref(0)),
])

# A watched eventfd held open by a dup: closing one descriptor is not the
# file's last reference, so no release runs and the item (keyed by the
# original fd) stays; the dup's ADD is a second item.
trace("e_release_eventfd_dup_held", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    dup(ref(1)),                               # 2: 10
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0
    write(ref(1), 8, 1),
    close(ref(1)),                             # 5: 0 (the file lives on through 10)
    wait(ref(0)),                              # 6: 1 [IN, 1]
    add(ref(0), ref(2), EPOLLIN, 2),           # 7: 0
    wait(ref(0)),                              # 8: 2 [IN, 1], [IN, 2]
    close(ref(2)),                             # 9: 0 (the last reference: both items go)
    wait(ref(0)),                              # 10: 0
    close(ref(0)),
])

# The hangup: closing a pipe's write end with the read end open takes
# pipe_release's wake (fs/pipe.c:734-736, key NULL) to the read end's item;
# the next wait polls EPOLLHUP (pipe_poll :689, writers 0 and f_pipe !=
# w_counter), delivered through the ERR|HUP bits ADD always sets (:2584).
trace("e_release_pipe_hup", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    add(ref(0), R(1), EPOLLIN, 1),             # 2: 0
    wait(ref(0)),                              # 3: 0
    close(W(1)),                               # 4: 0
    wait(ref(0)),                              # 5: 1 [HUP, 1]
    read(R(1), 8),                             # 6: 0 (EOF)
    wait(ref(0)),                              # 7: 1 [HUP, 1]
    close(ref(0)),
])

# The write end without readers: EPOLLOUT|EPOLLERR (pipe_poll :695-699); a
# write is -EPIPE with SIGPIPE pending (the pipes contract).
trace("e_release_pipe_err", [
    epoll_create1(),                           # 0: 8
    pipe2(),                                   # 1: 9, 10
    add(ref(0), W(1), EPOLLOUT, 1),            # 2: 0 (ready: OUT)
    wait(ref(0)),                              # 3: 1 [OUT, 1]
    close(R(1)),                               # 4: 0
    wait(ref(0)),                              # 5: 1 [OUT|ERR, 1]
    write(W(1), 1),                            # 6: -EPIPE, sigpipe 1
    wait(ref(0)),                              # 7: 1 [OUT|ERR, 1]
    close(ref(0)),
])

# Closing a set of three items: ep_clear_and_put's two walks in key order
# (:1116-1121 unregister, :1131-1136 remove); the files outlive the set.
trace("e_release_set_three", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    eventfd2(),                                # 2: 10
    pipe2(),                                   # 3: 11, 12
    add(ref(0), ref(1), EPOLLIN, 1),           # 4: 0
    add(ref(0), ref(2), EPOLLIN, 2),           # 5: 0
    add(ref(0), R(3), EPOLLIN, 3),             # 6: 0
    write(ref(1), 8, 1),
    write(W(3), 4),
    wait(ref(0)),                              # 9: 2 [IN, 1], [IN, 3]
    close(ref(0)),                             # 10: 0
    wait(ref(0)),                              # 11: -EBADF
    read(ref(1)),                              # 12: 8
    read(R(3), 4),                             # 13: 4
])

# The kind-308 one-off's subset (section 7): a recycled file slot between two
# fresh ones. Files 9, 10, 11 are allocated in order; closing 10 frees its
# struct file, and the next eventfd takes the free slab object back (the
# same address, between 9's and 11's) under descriptor 10. The set's items
# are inserted in the order 9, 11, 10, so the tree's key order (address) is
# 9, 10, 11 while the allocation order is 9, 11, 10: the close walks run in
# key order, which only the record fixes.
trace("e_close_three_recycled", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    eventfd2(),                                # 2: 10
    eventfd2(),                                # 3: 11
    close(ref(2)),                             # 4: 0
    eventfd2(),                                # 5: 10 (the recycled slot)
    add(ref(0), ref(1), EPOLLIN, 1),           # 6: 0
    add(ref(0), ref(3), EPOLLIN, 3),           # 7: 0
    add(ref(0), ref(5), EPOLLIN, 2),           # 8: 0
    write(ref(1), 8, 1),
    write(ref(3), 8, 1),
    write(ref(5), 8, 1),
    wait(ref(0)),                              # 12: 3 [1, 3, 2] (ready-list order: insertion)
    close(ref(0)),                             # 13: 0 (two walks in key order)
])

# dup3 over the set's descriptor: the set's file loses its last reference
# inside dup3 (filp_close), ep_clear_and_put runs, and the descriptor is now
# the eventfd: the wait is -EINVAL.
trace("e_release_dup3_over_set", [
    epoll_create1(),                           # 0: 8
    eventfd2(),                                # 1: 9
    write(ref(1), 8, 1),
    add(ref(0), ref(1), EPOLLIN, 1),           # 3: 0
    wait(ref(0)),                              # 4: 1 [IN, 1]
    dup3(ref(1), ref(0)),                      # 5: 8
    wait(ref(0)),                              # 6: -EINVAL
    read(ref(0)),                              # 7: 8
])


def render(t):
    return json.dumps(validate_trace(t), indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="verify the committed files instead of writing")
    args = parser.parse_args()
    expected = {f"{name}.json": render(t) for name, t in TRACES.items()}
    if args.check:
        present = {p.name: p.read_text() for p in OUT.glob("*.json")}
        if present != expected:
            stale = sorted(set(present) ^ set(expected) | {k for k in expected if present.get(k) != expected[k]})
            raise SystemExit(f"corpus/epoll differs from scripts/epoll-corpus.py: {stale}")
        print(f"corpus/epoll: {len(expected)} traces up to date")
        return
    OUT.mkdir(parents=True, exist_ok=True)
    for stale in set(p.name for p in OUT.glob("*.json")) - set(expected):
        (OUT / stale).unlink()
    for name, text in expected.items():
        (OUT / name).write_text(text)
    print(f"wrote {len(expected)} traces to {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
