#!/usr/bin/env python3
"""Writes the pipes stage-1 corpus into corpus/pipes (docs/2026-10-05-p-pipes.md
section 7, one trace per target).

Each trace's comment (TRACES below) says what Linux 6.12.110 does, with the
fs/pipe.c lines (and fs/inode.c, kernel/signal.c where named) that decide it;
the check compares the mirror against the real kernel, so a comment is a
statement of intent, not an oracle. The output is deterministic: rerunning
this script reproduces the committed files (`--check` verifies that without
writing).

Conventions: fds 0-7 are the guest's fixture files, so the first descriptor a
trace allocates is 8 (rlimit_nofile 32 unless stated). A write's buffer is the
trace contract's pattern (harness/trace.py): bytes 0-7 are `value`
little-endian, byte k >= 8 of operation i is (7i + 13k + 17(k >> 8)) mod 256,
so every byte read back is checked (the read's head and BLAKE2s digest).
`pause_ms` sleeps outside the coverage window before an operation: a 5 ms
pause spans a 4 ms coarse-clock tick (HZ=250), so that operation finds the
pipefs inode's stamps different from now (fs/inode.c:2100, 2225, 2229) and
reads the clock twice (section 3).
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness.trace import validate_trace  # noqa: E402

OUT = ROOT / "corpus" / "pipes"

O_WRONLY, O_NOTIFICATION_PIPE, O_NONBLOCK = 0o1, 0o200, 0o4000
O_DIRECT, O_NOATIME, O_CLOEXEC = 0o40000, 0o1000000, 0o2000000
NB = O_NONBLOCK
PAGE = 4096
MAX_IO = 69632


def R(i):
    """The read end (fd[0]) of the pipe2 at index i."""
    return {"pipe": i, "end": 0}


def W(i):
    """The write end (fd[1]) of the pipe2 at index i."""
    return {"pipe": i, "end": 1}


def ref(i):
    return {"ref": i}


def lit(n):
    return {"literal": n}


def pipe2(flags):
    return {"op": "pipe2", "flags": flags}


def eventfd2(init=0, flags=NB):
    return {"op": "eventfd2", "init": init, "flags": flags}


def write(fd, count, value=0x0123456789abcdef, pause=None):
    op = {"op": "write", "fd": fd, "count": count, "value": str(value)}
    if pause:
        op["pause_ms"] = pause
    return op


def read(fd, count, pause=None):
    op = {"op": "read", "fd": fd, "count": count}
    if pause:
        op["pause_ms"] = pause
    return op


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


# Create, write 5, read 5, F_GETFL on both ends. pipe2(O_NONBLOCK|O_DIRECT):
# the writer gets O_WRONLY | (flags & (O_NONBLOCK|O_DIRECT)) (:938-940), the
# reader O_RDONLY | (flags & O_NONBLOCK) (:950-951), so F_GETFL gives 0o4000
# on the read end and 0o44001 on the write end. The write is one packet
# (is_packetized, :534); the read returns its 5 bytes; the next read finds
# the pipe empty with a writer: -EAGAIN (:356-359).
trace("p_basic", [
    pipe2(NB | O_DIRECT),                      # 0: fds [8, 9]
    write(W(0), 5, 0x1122334455667788),        # 1: 5
    read(R(0), 5),                             # 2: 5, bytes 88 77 66 55 44
    read(R(0), 5),                             # 3: -EAGAIN
    fcntl(R(0), "F_GETFL"),                    # 4: O_RDONLY|O_NONBLOCK
    fcntl(W(0), "F_GETFL"),                    # 5: O_WRONLY|O_NONBLOCK|O_DIRECT
    close(R(0)),
    close(W(0)),
])

# The flag mask (:970): 1 and 2^31 are outside O_CLOEXEC|O_NONBLOCK|O_DIRECT|
# O_NOTIFICATION_PIPE: -EINVAL before anything is allocated. O_NOTIFICATION_PIPE
# (O_EXCL) passes the mask; create_pipe_files allocates the inode (one clock
# record, simple_inode_init_ts) and the pipe, then watch_queue_init is the
# CONFIG_WATCH_QUEUE=n stub: -ENOPKG, free_pipe_info and iput (:929-935). No
# descriptor is consumed, so the next pipe2 gets [8, 9]; a failed pipe2's ends
# resolve to -1 (-EBADF).
trace("p_flags", [
    pipe2(1),                                  # 0: -EINVAL
    pipe2(O_NOTIFICATION_PIPE),                # 1: -ENOPKG
    pipe2(2 ** 31),                            # 2: -EINVAL
    pipe2(NB | O_NOTIFICATION_PIPE),           # 3: -ENOPKG
    pipe2(NB),                                 # 4: [8, 9]
    write(W(1), 8),                            # 5: -EBADF (the -ENOPKG pipe has no ends)
    write(W(4), 8),                            # 6: 8
    read(R(4), 8),                             # 7: 8
    close(W(4)),
    close(R(4)),
])

# O_CLOEXEC lands on both descriptors (get_unused_fd_flags(flags), :977-985):
# F_GETFD gives FD_CLOEXEC on both ends, 0 on a pipe created without it.
trace("p_cloexec", [
    pipe2(NB | O_CLOEXEC),                     # 0: [8, 9]
    fcntl(R(0), "F_GETFD"),                    # 1: 1
    fcntl(W(0), "F_GETFD"),                    # 2: 1
    pipe2(NB),                                 # 3: [10, 11]
    fcntl(R(3), "F_GETFD"),                    # 4: 0
    fcntl(W(3), "F_GETFD"),                    # 5: 0
    fcntl(W(0), "F_SETFD", 0),                 # 6: 0
    fcntl(W(0), "F_GETFD"),                    # 7: 0
    fcntl(R(0), "F_GETFL"),                    # 8: O_RDONLY|O_NONBLOCK (O_CLOEXEC is not a file flag)
])

# rlimit_nofile 8: fds 0-7 are taken, so the first get_unused_fd_flags fails
# (:978-979, -EMFILE); err_read_pipe (:997-999) fputs both files, whose
# __fput (two pipe_releases, the read end's i_readcount_dec, the dentry's
# last dput and the inode's iput) runs in the operation's task work.
trace("p_emfile_first_fd", [
    pipe2(NB),                                 # 0: -EMFILE
    pipe2(0),                                  # 1: -EMFILE (blocking flags fail the same way)
    pipe2(O_NOTIFICATION_PIPE),                # 2: -ENOPKG (create_pipe_files fails before any fd)
    pipe2(1),                                  # 3: -EINVAL
], rlimit_nofile=8)

# rlimit_nofile 9: the first get_unused_fd_flags gets 8, the second fails
# (:983-984); put_unused_fd(fdr), then both files are fput and released in
# task work (two pipe_releases in one operation). fd 8 is free again: the
# eventfd gets it.
trace("p_emfile_second_fd", [
    pipe2(NB),                                 # 0: -EMFILE
    pipe2(NB | O_DIRECT),                      # 1: -EMFILE
    eventfd2(),                                # 2: 8
    pipe2(NB),                                 # 3: -EMFILE (no fd at all now)
    close(ref(2)),                             # 4: 0
    pipe2(NB),                                 # 5: -EMFILE again (one fd free)
], rlimit_nofile=9)

# F_SETPIPE_SZ 4096 first: one slot (round_pipe_size, pipe_resize_ring), so a
# write that takes a slot instead of merging shows as -EAGAIN. Write 100: a
# CAN_MERGE buffer of 100 bytes. Write 4000: chars = 4000, 100 + 4000 > 4096
# at :480, no merge, and the ring is full: -EAGAIN with ret == 0 (:559).
# Write 3996: 100 + 3996 <= 4096, the exact fit merges (:480-495) and
# returns. Write 1: 4096 + 1 > 4096, full: -EAGAIN. The read returns the one
# page in order.
trace("p_merge_vs_slot", [
    pipe2(NB),                                 # 0
    fcntl(W(0), "F_SETPIPE_SZ", PAGE),         # 1: 4096
    write(W(0), 100),                          # 2: 100
    write(W(0), 4000),                         # 3: -EAGAIN
    write(W(0), 3996),                         # 4: 3996 (merge, exact fit)
    write(W(0), 1),                            # 5: -EAGAIN
    read(R(0), MAX_IO),                        # 6: 4096
    write(W(0), 1),                            # 7: 1 (a fresh slot: the ring is empty)
    read(R(0), 8),                             # 8: 1
])

# Write 4097 to an empty pipe: chars = 4097 & 4095 = 1, but was_empty skips
# the merge (:474); two slots (4096 + 1). Write 1 merges into the second slot
# (offset 1 + 1 <= 4096). Read 4098 crosses the slot boundary.
trace("p_page_boundary", [
    pipe2(NB),                                 # 0
    write(W(0), PAGE + 1),                     # 1: 4097
    write(W(0), 1),                            # 2: 1 (merged)
    read(R(0), PAGE + 2),                      # 3: 4098
    read(R(0), 1),                             # 4: -EAGAIN
])

# The default ring has 16 slots: 16 writes of 4096 fill it (pipe_full,
# :506/:553), the 17th gets -EAGAIN with ret == 0 (:559). A read frees a slot
# and takes the was_full wake arm (:401); the next write succeeds.
trace("p_fill_default",
      [pipe2(NB)] + [write(W(0), PAGE, k) for k in range(16)] + [
          write(W(0), PAGE),                   # 17: -EAGAIN
          read(R(0), PAGE),                    # 18: 4096
          write(W(0), PAGE),                   # 19: 4096
          read(R(0), MAX_IO),                  # 20: 65536
          read(R(0), 1),                       # 21: -EAGAIN
      ])

# One write of 69632 to an empty pipe fills the 16 slots and returns the
# partial count 65536 (:559 not taken: ret != 0). The next write: -EAGAIN.
# The read of 69632 drains 65536.
trace("p_overfill_single", [
    pipe2(NB),                                 # 0
    write(W(0), MAX_IO),                       # 1: 65536
    write(W(0), 1),                            # 2: -EAGAIN
    read(R(0), MAX_IO),                        # 3: 65536
    read(R(0), 1),                             # 4: -EAGAIN
])

# O_DIRECT (packet mode): every write is its own PIPE_BUF_FLAG_PACKET buffer
# and never merges. Read 3 of a 10-byte packet returns 3 and discards the
# other 7 (:338-341); read 100 returns the next packet's 20 and stops there;
# then -EAGAIN. Sixteen one-byte packets fill the ring (16 bytes in 16
# slots); the 17th: -EAGAIN; a read returns one byte.
trace("p_packet",
      [pipe2(NB | O_DIRECT),                   # 0
       write(W(0), 10, 0x0a0b0c0d0e0f1011),    # 1: 10
       write(W(0), 20, 0x2122232425262728),    # 2: 20
       read(R(0), 3),                          # 3: 3
       read(R(0), 100),                        # 4: 20
       read(R(0), 100)]                        # 5: -EAGAIN
      + [write(W(0), 1, k) for k in range(16)]  # 6-21: 1 each
      + [write(W(0), 1),                       # 22: -EAGAIN
         read(R(0), 100),                      # 23: 1
         read(R(0), 100)])                     # 24: 1

# F_SETFL O_DIRECT on the write end mid-trace (setfl: S_ISFIFO skips the
# FMODE_CAN_ODIRECT test, fs/fcntl.c:61-64). A CAN_MERGE buffer written
# before the F_SETFL still takes small writes (:479 tests the buffer's flag,
# not the file's mode); a write that needs a new slot gets a packet buffer.
# Read 100 drains the 18 merged bytes and 82 of the packet, and discards the
# packet's rest. On a second pipe, O_DIRECT on the read end changes nothing:
# is_packetized tests the writing file (:534), so the writes merge.
trace("p_packet_setfl", [
    pipe2(NB),                                 # 0
    write(W(0), 10),                           # 1: 10 (CAN_MERGE)
    fcntl(W(0), "F_SETFL", NB | O_DIRECT),     # 2: 0
    fcntl(W(0), "F_GETFL"),                    # 3: O_WRONLY|O_NONBLOCK|O_DIRECT
    write(W(0), 5),                            # 4: 5 (merged into the CAN_MERGE buffer)
    write(W(0), 3),                            # 5: 3 (merged)
    write(W(0), PAGE),                         # 6: 4096 (a packet slot: chars == 0, no merge)
    read(R(0), 100),                           # 7: 100 (18 + 82; the packet's rest is dropped)
    read(R(0), 100),                           # 8: -EAGAIN
    pipe2(NB),                                 # 9
    fcntl(R(9), "F_SETFL", NB | O_DIRECT),     # 10: 0
    fcntl(R(9), "F_GETFL"),                    # 11: O_RDONLY|O_NONBLOCK|O_DIRECT
    write(W(9), 10),                           # 12: 10
    write(W(9), 10),                           # 13: 10 (merged: the writer is not packetized)
    read(R(9), 100),                           # 14: 20
])

# F_GETPIPE_SZ is max_usage * PAGE_SIZE (65536 by default). F_SETPIPE_SZ 4096
# gives one slot; with one full slot a write of 1 gets -EAGAIN. 8192 grows
# it. 0 and 4095 round up to one page (round_pipe_size :1253) and shrink to
# the one occupied slot (nr_slots < n is false at :1282). 4097 rounds up to
# 8192 (roundup_pow_of_two, :1256). 2^31 + 1 and 2^32 - 1 exceed 1U << 31
# (:1249): round_pipe_size returns 0 and pipe_set_size -EINVAL (:1347)
# without allocating (2^31 itself would kcalloc 8 MiB and fail: excluded).
# 1048577 rounds to 2 MiB, above pipe_max_size; root passes the capable test
# (:1357-1359). On an eventfd both commands give -EBADF (get_pipe_info,
# :1390).
trace("p_resize", [
    pipe2(NB),                                 # 0
    fcntl(W(0), "F_GETPIPE_SZ"),               # 1: 65536
    fcntl(W(0), "F_SETPIPE_SZ", PAGE),         # 2: 4096
    write(W(0), PAGE),                         # 3: 4096
    write(W(0), 1),                            # 4: -EAGAIN
    fcntl(W(0), "F_SETPIPE_SZ", 2 * PAGE),     # 5: 8192
    fcntl(R(0), "F_GETPIPE_SZ"),               # 6: 8192
    fcntl(W(0), "F_SETPIPE_SZ", 0),            # 7: 4096
    fcntl(W(0), "F_SETPIPE_SZ", PAGE - 1),     # 8: 4096
    fcntl(W(0), "F_SETPIPE_SZ", PAGE + 1),     # 9: 8192
    fcntl(W(0), "F_GETPIPE_SZ"),               # 10: 8192
    fcntl(W(0), "F_SETPIPE_SZ", 2 ** 31 + 1),  # 11: -EINVAL
    fcntl(W(0), "F_SETPIPE_SZ", 2 ** 32 - 1),  # 12: -EINVAL
    fcntl(W(0), "F_SETPIPE_SZ", 1048577),      # 13: 2097152
    fcntl(R(0), "F_GETPIPE_SZ"),               # 14: 2097152
    eventfd2(),                                # 15
    fcntl(ref(15), "F_SETPIPE_SZ", PAGE),      # 16: -EBADF
    fcntl(ref(15), "F_GETPIPE_SZ"),            # 17: -EBADF
    read(R(0), MAX_IO),                        # 18: 4096
    fcntl(W(0), "F_SETPIPE_SZ", 4194304),      # 19: 4194304 (the 4 MiB cap of the generator)
])

# Three full slots; shrinking to two: nr_slots 2 < n 3 at :1282, -EBUSY. A
# read frees one; the retry shrinks to exactly the occupancy (2 < 2 is
# false) and succeeds.
trace("p_resize_ebusy", [
    pipe2(NB),                                 # 0
    write(W(0), PAGE),                         # 1
    write(W(0), PAGE),                         # 2
    write(W(0), PAGE),                         # 3
    fcntl(W(0), "F_SETPIPE_SZ", 2 * PAGE),     # 4: -EBUSY
    read(R(0), PAGE),                          # 5: 4096
    fcntl(W(0), "F_SETPIPE_SZ", 2 * PAGE),     # 6: 8192
    fcntl(W(0), "F_GETPIPE_SZ"),               # 7: 8192
    write(W(0), 1),                            # 8: -EAGAIN (two full slots)
    read(R(0), MAX_IO),                        # 9: 8192, in order
])

# A one-slot ring: five write/read pairs move head and tail past ring_size;
# every dereference masks with ring_size - 1 (:306, :476, :529). Then a
# resize while wrapped: h = head & 0 = 0 <= t = 0, so pipe_resize_ring takes
# the two-memcpy arm (:1298-1304) with tsize = 1.
trace("p_wrap",
      [pipe2(NB), fcntl(W(0), "F_SETPIPE_SZ", PAGE)]
      + [op for k in range(5) for op in (write(W(0), 1, k + 1), read(R(0), 1))]
      + [write(W(0), 3),                       # 12: 3
         fcntl(W(0), "F_SETPIPE_SZ", 2 * PAGE),  # 13: 8192
         write(W(0), PAGE),                    # 14: 4096 (chars == 0: no merge, the second slot)
         read(R(0), MAX_IO),                   # 15: 4099
         read(R(0), 1)])                       # 16: -EAGAIN

# The default ring: fill 16 slots, read 2, write 2: head = 18, tail = 2, so
# h = 2 <= t = 2 and pipe_resize_ring copies bufs[2..16) then bufs[0..2)
# (:1300-1304). After growing to 32 slots the read returns all 65536 bytes;
# the digest checks the order.
trace("p_resize_wrapped_copy",
      [pipe2(NB)] + [write(W(0), PAGE, k) for k in range(16)] + [
          read(R(0), PAGE),                    # 17
          read(R(0), PAGE),                    # 18
          write(W(0), PAGE, 100),              # 19
          write(W(0), PAGE, 101),              # 20
          fcntl(W(0), "F_SETPIPE_SZ", 131072),  # 21: 131072
          fcntl(W(0), "F_GETPIPE_SZ"),         # 22: 131072
          read(R(0), MAX_IO),                  # 23: 65536
          read(R(0), 1),                       # 24: -EAGAIN
      ])

# The one-deep page cache: a buffer released while tmp_page is empty and its
# page_count is 1 is kept (anon_pipe_buf_release, :125-126); the next slot
# uses it (:509-512). With two buffers released while one page is cached,
# the second page is put (:128).
trace("p_tmp_page", [
    pipe2(NB),                                 # 0
    write(W(0), 100),                          # 1: 100 (alloc_page)
    read(R(0), 100),                           # 2: 100 (page cached in tmp_page)
    write(W(0), 100),                          # 3: 100 (tmp_page used)
    write(W(0), PAGE),                         # 4: 4096 (chars == 0: a new slot, alloc_page)
    read(R(0), MAX_IO),                        # 5: 4196 (first page cached, second put)
    write(W(0), 1),                            # 6: 1 (tmp_page used)
    read(R(0), 1),                             # 7: 1
])

# No reader: -EPIPE with SIGPIPE (:457-461). The guest blocks SIGPIPE, so
# send_sig adds it to the pending set (prepare_signal sees it blocked;
# complete_signal wakes nobody) and the write reports sigpipe 1. A second
# -EPIPE finds it pending: legacy_queue (kernel/signal.c:1094) returns
# early; still 1. A zero-byte write returns 0 before the readers test (:452).
trace("p_epipe", [
    pipe2(NB),                                 # 0
    write(W(0), 10),                           # 1: 10, sigpipe 0
    close(R(0)),                               # 2: 0 (the last reader: pipe_release)
    write(W(0), 10),                           # 3: -EPIPE, sigpipe 1
    write(W(0), 10),                           # 4: -EPIPE (legacy_queue), sigpipe 1
    write(W(0), 0),                            # 5: 0, sigpipe 1 (still pending)
    close(W(0)),                               # 6: 0 (the last file: free_pipe_info, iput)
])

# No writer: a read drains what is left, then returns 0 (EOF, :352-353), even
# on a blocking pipe (the writers test precedes the O_NONBLOCK test). Zero-
# byte reads and writes return 0 at once (:260, :452).
trace("p_eof", [
    pipe2(NB),                                 # 0
    write(W(0), 5),                            # 1: 5
    close(W(0)),                               # 2: 0
    read(R(0), 100),                           # 3: 5
    read(R(0), 100),                           # 4: 0 (EOF)
    pipe2(0),                                  # 5: a blocking pipe
    write(W(5), 0),                            # 6: 0
    read(R(5), 0),                             # 7: 0
    close(W(5)),                               # 8: 0
    read(R(5), 10),                            # 9: 0 (EOF, no wait)
])

# The wrong end: a write to the read end and a read of the write end fail in
# vfs_write/vfs_read before the pipe is reached (fs/read_write.c:667-668,
# 553-554: FMODE_WRITE/FMODE_READ clear, -EBADF). The early returns jump into
# the functions' shared exits, whose KCOV points the line table attributes to
# read_write.c:567 and to file_end_write's not-regular test (fs.h:3018)
# inlined at :691 (correspondence/kcov.json `shared_exits`). Zero-byte forms
# fail the same way: the mode tests precede everything.
trace("p_wrong_end", [
    pipe2(NB),                                 # 0
    write(R(0), 10),                           # 1: -EBADF, sigpipe 0
    read(W(0), 10),                            # 2: -EBADF
    write(R(0), 0),                            # 3: -EBADF
    read(W(0), 0),                             # 4: -EBADF
    write(W(0), 10),                           # 5: 10 (the right end still works)
    read(R(0), 10),                            # 6: 10
    close(R(0)),                               # 7: 0
    close(W(0)),                               # 8: 0
])

# readers/writers count files, not descriptors: dup the read end and close
# the original, the file stays open (readers 1). dup3 over a pipe end drops
# that file's last reference: its __fput (pipe_release, readers 0) is
# deferred to the operation's task work; the next write gets -EPIPE.
trace("p_dup_ends", [
    pipe2(NB),                                 # 0: [8, 9]
    dup(R(0)),                                 # 1: 10
    close(R(0)),                               # 2: 0
    write(W(0), 7),                            # 3: 7
    read(ref(1), 7),                           # 4: 7
    dup3(W(0), lit(20)),                       # 5: 20
    close(W(0)),                               # 6: 0
    write(ref(5), 3),                          # 7: 3
    eventfd2(),                                # 8: 8
    dup3(ref(8), ref(1)),                      # 9: 10 (replaces the last read-end file)
    write(ref(5), 3),                          # 10: -EPIPE, sigpipe 1
    read(ref(9), 8),                           # 11: -EAGAIN (an eventfd now, count 0)
])

# An eventfd and a pipe in one trace: the pipe commands on an eventfd give
# -EBADF; an eventfd read with a 69632-byte buffer returns its 8 bytes.
trace("p_mixed", [
    eventfd2(0),                               # 0: 8
    pipe2(NB),                                 # 1: [9, 10]
    write(ref(0), 8, 5),                       # 2: 8
    fcntl(ref(0), "F_SETPIPE_SZ", PAGE),       # 3: -EBADF
    fcntl(ref(0), "F_GETPIPE_SZ"),             # 4: -EBADF
    read(ref(0), MAX_IO),                      # 5: 8 (value 5)
    write(W(1), 8, 7),                         # 6: 8
    read(R(1), MAX_IO),                        # 7: 8
    fcntl(ref(0), "F_GETFL"),                  # 8: O_RDWR|O_NONBLOCK
    close(ref(0)),
    close(R(1)),
    close(W(1)),
])

# F_SETFL O_NOATIME on the read end (fs/fcntl.c:51-53: the owner test passes,
# i_uid is the creator's fsuid). file_accessed skips touch_atime
# (include/linux/fs.h:2578): no clock record. Cleared again, the read reads
# the clock. O_NOATIME on the write end does not affect file_update_time.
trace("p_noatime", [
    pipe2(NB),                                 # 0
    write(W(0), 10),                           # 1: 10
    fcntl(R(0), "F_SETFL", NB | O_NOATIME),    # 2: 0
    fcntl(R(0), "F_GETFL"),                    # 3: O_RDONLY|O_NONBLOCK|O_NOATIME
    read(R(0), 5, pause=5),                    # 4: 5, no clock record
    fcntl(R(0), "F_SETFL", NB),                # 5: 0
    read(R(0), 5, pause=5),                    # 6: 5, two clock records (atime updated)
    fcntl(W(0), "F_SETFL", NB | O_NOATIME),    # 7: 0
    write(W(0), 4, pause=5),                   # 8: 4, two clock records (mtime and ctime updated)
    read(R(0), 4),                             # 9: 4
])

# Stamps and the clock. A 5 ms pause before an operation puts it in a later
# tick than the last stamp: the write finds mtime and ctime different
# (fs/inode.c:2225, 2229) and updates both (a second clock read at 1997);
# the read finds atime different (2100) and updates it (2007). The
# operations without a pause may fall into the same tick (one record, the
# "equal" outcome) or not; the check reports which happened.
trace("p_ticks", [
    pipe2(NB),                                 # 0: one record (creation)
    write(W(0), 10, pause=5),                  # 1: 10, two records
    write(W(0), 10),                           # 2: 10, one or two
    write(W(0), 10, pause=5),                  # 3: 10, two records
    read(R(0), 5, pause=5),                    # 4: 5, two records
    read(R(0), 5),                             # 5: 5, one or two
    read(R(0), 5, pause=5),                    # 6: 5, two records
    write(W(0), 1, pause=5),                   # 7: 1, two records
    read(R(0), 100),                           # 8: 16, one or two
    read(R(0), 100, pause=5),                  # 9: -EAGAIN, no record (ret <= 0)
    write(W(0), 0, pause=5),                   # 10: 0, no record (total_len == 0)
    write(W(0), 1, pause=5),                   # 11: 1, two records
    write(W(0), 1),                            # 12: 1, one or two
    read(R(0), 2, pause=5),                    # 13: 2, two records
])

# The hang control: a blocking pipe, a read on an empty pipe with a writer
# would wait (pipe_read :361-395, outside stage 1). The domain filter
# excludes the trace (unsupported), so it never reaches the guest; the
# `pipes` suite requires that.
trace("p_blocking_filtered", [
    pipe2(0),                                  # 0: a blocking pipe
    write(W(0), 10),                           # 1: 10 (space: no wait)
    read(R(0), 10),                            # 2: 10 (data: no wait)
    read(R(0), 10),                            # 3: would block
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
            raise SystemExit(f"corpus/pipes differs from scripts/pipes-corpus.py: {stale}")
        print(f"corpus/pipes: {len(expected)} traces up to date")
        return
    OUT.mkdir(parents=True, exist_ok=True)
    for stale in set(p.name for p in OUT.glob("*.json")) - set(expected):
        (OUT / stale).unlink()
    for name, text in expected.items():
        (OUT / name).write_text(text)
    print(f"wrote {len(expected)} traces to {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
