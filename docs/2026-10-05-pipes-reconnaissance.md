# Pipes as the scale test — reconnaissance, 2026-10-05 [AGENT]

Read-only reconnaissance by a Fable agent, run while the D2 mutants were
running. Its question: does a first pipes stage need any new kernel
instrumentation (roadmap step 7, "the next subsystem needs only
declarations", choice-stream strategy section 10)? Paths are relative to
the repository; kernel paths are under `.deps/linux` (6.12.110). The guest
config is `kernel/config-x86_64-net-choice`.

## Verdict

**Pipes need zero new kernel hooks.** Every hidden input on the `pipe2`,
`read`, `write`, `close`, `dup` and `fcntl` paths is one of three things:
- **The coarse real-time clock**, `ktime_get_coarse_real_ts64`. It is
  already captured (kind 215, 16 bytes) and consumed through
  `current_time` (`fs/inode.c:2644-2650`). That makes one new mirror site at
  `fs/inode.c:2648`.
- **An allocation**, assumed successful today (`EnvSite`; fault injection is
  roadmap step 5).
- **Deterministic kernel state**: the signal pending set, and per-user page
  accounting.

The paths have no other hidden inputs:
- No random draws. The guest config disables freelist randomization, page
  shuffling and random kmalloc caches, and `get_next_ino` is a counter.
- No deferred work, no timers, and no RCU-visible frees (pipefs uses
  `free_inode_nonrcu`, and `d_alloc_pseudo` sets `DCACHE_NORCU`).
- No scheduling in single-task traces that never block.

`DISPATCH_SYMBOLS` is unchanged.

**What strains the strict "declarations only" reading.** None of it is a
kernel hook.
1. **Harness and trace-contract code:**
   - a producer that returns two fds (`pipe2` returns 0 and writes the fds to
     user memory);
   - an I/O buffer above 16 bytes, with a read observation to match. Filling
     a 16-slot pipe to `-EAGAIN` takes at least 65,537 bytes;
   - SIGPIPE: block it in the trace child and observe it with `sigpending`,
     because today the guest installs no disposition;
   - errno allowlists.
2. **Two existing mirror collapses that pipes force open:**
   - `put_file_access`'s read-only arm (`unsupported "i_readcount_dec"`;
     `CONFIG_FILE_LOCKING=y` makes it real);
   - `vfs_write`'s `write_iter` arm (`unsupported "new_sync_write"`).
3. **One environment fact of the `nr_files` class:** `user->pipe_bufs`, a
   KCOV comparison operand in `too_many_pipe_buffers_soft`. Either track it
   from a runner baseline or exclude it from A3, as with `nr_files`.

## Why pipes, not epoll, as the scale test

Epoll also needs no new hooks, but for a weaker reason: its paths have
almost no hidden input. `epoll_wait` with timeout 0 reads no clock, and
otherwise the values reach nothing observable. So epoll says little about
the capture claim. What epoll forces instead is modeling wait-queue entries
and callbacks: `ep_poll_callback`, and `kernel/sched/wait.c` as mirror code.

Pipes are smaller (`fs/pipe.c` has 1,522 lines; `fs/eventpoll.c` has 2,838)
and shaped like the eventfd slice. Of the two, they are the only subsystem
whose hidden input, the coarse clock, flows into mirror state and decides
later branches: `timespec64_equal` on atime, mtime and ctime. With HZ=250
both outcomes arise naturally. That is exactly the generic-capture claim
under test, with A3 operand evidence.

Epoll is the better **second** step: epoll over eventfd and pipe tests the
wait-queue cut discipline and `pipe_poll`.

## Stage-1 scope

- **`pipe2`:** the flag mask, `create_pipe_files`, `get_pipe_inode` (one
  clock read), `alloc_file_pseudo`/`alloc_file_clone`, `stream_open` twice,
  and the `O_NOTIFICATION_PIPE` → `-ENOPKG` arm.
- **`read` (`pipe_read`):** the ring loop, `PIPE_BUF_FLAG_PACKET`,
  `anon_pipe_buf_release` and its one-deep page cache, EOF, `-EAGAIN`, the
  wakeup epilogue, and `touch_atime` (one or two clock reads).
- **`write` (`new_sync_write` → `pipe_write`):** SIGPIPE/`-EPIPE`, merging
  into the last buffer, the slot loop with `alloc_page`, `O_DIRECT` packet
  mode, `-EAGAIN`, and `file_update_time` (one or two clock reads).
- **`close`, `dup` and `fcntl`:** `pipe_release` and `free_pipe_info`;
  `F_SETFL O_DIRECT`; `F_SETPIPE_SZ`/`F_GETPIPE_SZ` (ring resize, `-EBUSY`,
  and `-EBADF` for a non-pipe such as an eventfd).
- **Out of stage 1:** blocking waits (they would need a second task),
  `poll`, `FIONREAD`, `FASYNC`/SIGIO, splice/vmsplice/tee, named FIFOs.

## Size and risks

- **Size:** about 1,000–1,100 new Lean lines (`FS/Pipe.lean`,
  `FS/Inode.lean`, edits elsewhere), with 100–120 decisions. The harness
  needs about 180 lines across `guest.c`, `trace.py`, `protocol.py`,
  `linux.py` and `generate.py`. `kcov.json` gains `fs/pipe.c`,
  `pipe_fs_i.h`, `fs/inode.c` and `time64.h`, with about 20 functions.
- **Risk: a wrong ring model hangs Linux** (a mispredicted "no block"). It
  is loud, but costs a VM run.
- **Risk: `current_time` is one site for the whole kernel.** Any other inode
  timestamp read inside an operation becomes a hidden mismatch. That is
  fail-noisy and correct.
- **Risk: A3 on inline header comparisons** (`timespec64_equal`, `clamp`).
- **Risk: the `pipe_bufs` baseline** is unknown until the first operand
  records come in.
- **Risk: observation volume** for reads of up to 64 KiB. A capped hex plus
  digest scheme is a contract decision for the user.
- **When the zero-hook claim is tested again:** first by `FASYNC`/SIGIO and
  by any blocking stage with two tasks.
