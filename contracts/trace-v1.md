# FD/eventfd/pipe experiment contract, version 1

This contract fixes the initial experiment domain and observable results. Schema
files describe syntax; the additional validity rules below are normative. Changes
to this domain or comparison require a separately reviewed contract revision.

## Input

A JSON object has exactly `version` (1), `id` (a nonempty ASCII identifier of at
most 80 characters), and `ops` (1–64 operations). Identifiers use letters, digits,
underscore, dash, and dot. Unknown fields are errors. Operation forms are:

```json
{"op":"eventfd2","init":0,"flags":526336}
{"op":"dup","fd":{"ref":0}}
{"op":"dup3","fd":{"ref":0},"newfd":{"literal":9},"flags":0}
{"op":"close","fd":{"ref":1}}
{"op":"read","fd":{"ref":0},"count":8}
{"op":"write","fd":{"ref":0},"count":8,"value":"5"}
{"op":"fcntl","fd":{"ref":0},"cmd":"F_GETFD","arg":0}
```

All integer JSON values must be integers, excluding booleans. `init`, `flags`,
and `arg` are unsigned 32-bit values. `count` is 0–69632 (`MAX_IO`, 17 pages;
amended for pipes, below; it was 0–16). A write value is a canonical unsigned
decimal string in 0–18446744073709551615, with no leading zero except `"0"`. It
supplies bytes 0–7 of the write buffer, little-endian; byte `k ≥ 8` of the
write at operation index `i` is `(7·i + 13·k + 17·(k >> 8)) mod 256`, computed
identically by the guest and the mirror, so nothing beyond `value` crosses the
wire. Reads use a buffer initialized to `0xa5`; only the bytes actually
returned are observed (see Output). Faulting pointers are outside the domain.

Descriptor arguments contain exactly one of `literal` or `ref`. Literals are
signed 32-bit integers and must be negative or at least 8. References name an
earlier operation index whose operation is `eventfd2`, `dup`, or `dup3` (or
`epoll_create1`, amended 2026-10-12, below). A
successful producer supplies its original numeric result; closing that number
does not invalidate the reference. A failed producer supplies the deliberately
invalid number -1. Forward references and references to other operation kinds
are invalid inputs. These rules are applied equally by the guest and mirror.

`fcntl.cmd` is one of `F_GETFD`, `F_SETFD`, `F_GETFL`; getters may carry any
`arg`, which the kernel ignores. Creation may omit `EFD_NONBLOCK` (2048): a
blocking eventfd is in the domain as long as no operation on it would wait (a
read of an empty counter, or a write that does not fit). The mirror decides
this (a wait is `Stop.outsideDomain`); generated traces are filtered through
the mirror, and a trace in which Linux would block times out rather than
passing. Ordinary/semaphore mode is selected by bit 0. `EFD_CLOEXEC` is 524288.
(Amended 2026-09-29, Phase 4: the earlier contract required `EFD_NONBLOCK` and
zero getter arguments. The amendment only widens the domain; every earlier
trace remains valid.)

A trace may set `rlimit_nofile` (8–1024, default 32): the fixture sets both
`RLIMIT_NOFILE` bounds to it before the first operation, so descriptors up to
`rlimit_nofile - 1` are usable and the descriptor table can grow beyond its
initial 64 slots. (Amended 2026-09-29, Phase 4.)
Duplication flags may be any unsigned 32-bit pattern, so invalid-flag behavior is
observable. Flags reach kernel `int` arguments by their low 32 bits; literal FDs
are sign-extended to the x86-64 argument register, with kernel parameter casts
preserved by the mirror. There are no implicit retries.

## Pipes (amended 2026-10-06, workstream P)

The amendment widens the domain; every earlier trace remains valid. The design
is `docs/2026-10-05-p-pipes.md`, section 6.

- **`{"op":"pipe2","flags":u32}`** creates an anonymous pipe. A descriptor
  argument may be `{"pipe": i, "end": 0}` (the read end, `fd[0]`) or
  `{"pipe": i, "end": 1}` (the write end, `fd[1]`), where `i` names an earlier
  `pipe2`. `{"ref": i}` must still name an `eventfd2`, `dup` or `dup3`; a `ref`
  to a `pipe2` is invalid. A failed `pipe2` resolves both ends to -1.
- **`fcntl.cmd`** also accepts `F_SETFL` (Phase 4), `F_SETPIPE_SZ` (1031) and
  `F_GETPIPE_SZ` (1032); `arg` stays an unsigned 32-bit value.
- **`"pause_ms": 1–20`** may be added to any operation: the guest sleeps that
  long immediately before the operation's coverage reset, outside every
  window. The mirror ignores it. It makes coarse-clock ticks (4 ms, `HZ=250`)
  deterministic between operations.
- **Signals.** The trace child blocks `SIGPIPE` before the first operation
  and fails the trace if any signal is pending then. A write to a pipe without
  readers therefore leaves `SIGPIPE` pending (it is never delivered); any
  other pending signal is an environment failure.
- **Blocking.** A pipe may be created without `O_NONBLOCK`, as long as no
  operation would wait, under the same rule as blocking eventfds (the mirror
  decides; generated traces are filtered; the guest's parent kills a child
  that hangs and the batch fails).
- **Wire.** Opcode 14 is `pipe2`; descriptor kinds 2 and 3 are the read and
  write ends with the producer's index as value; `pause_ms` is the ninth field
  of every operation line (0 when absent).

## Epoll (amended 2026-10-12, epoll stream R)

The amendment widens the domain; every earlier trace remains valid. The design
is `docs/2026-10-12-epoll-design.md`, section 6 (tier 1).

- **`{"op":"epoll_create1","flags":u32}`** creates an epoll set. It is a
  descriptor producer: `{"ref": i}` may name an earlier `epoll_create1` as it
  may an `eventfd2`, `dup` or `dup3`.
- **`{"op":"epoll_ctl","epfd":fd,"cmd":u32,"fd":fd,"events":u32,"data":u64}`**
  is `epoll_ctl(epfd, cmd, fd, &event)` with `event = {events, data}`. `epfd`
  and `fd` take the descriptor forms above (`literal`, `ref`, `pipe`/`end`).
  `cmd` is the kernel's operation number (1 `EPOLL_CTL_ADD`, 2 `EPOLL_CTL_DEL`,
  3 `EPOLL_CTL_MOD`; any other value is observable as `-EINVAL`); `data` is a
  canonical unsigned decimal string like a write's `value`, copied back
  verbatim by the kernel, so the events a wait returns are fully predicted.
- **`{"op":"epoll_wait","epfd":fd,"maxevents":int,"timeout":int}`** is
  `epoll_wait(epfd, events, maxevents, timeout)`. Tier 1 accepts `maxevents`
  1–16 and `timeout` 0 only; other values are explicitly unsupported (no
  sleep record exists yet, design 9.1), not invalid.
- **Observation.** A successful `epoll_wait` returns its `ret` events through
  the read channel: the event buffer is initialised to `0xa5`, `bytes` is the
  first `min(12·ret, 64)` bytes of the packed `epoll_event` array (12 bytes
  each on x86-64: `events` u32, `data` u64) and `digest` the BLAKE2s-256 of
  all `12·ret` bytes, `null` when `ret ≤ 0`. The other two operations carry
  only `ret` and `errno`.
- **Fixture.** Once per boot, before the first trace, the guest adds a
  throwaway eventfd to a throwaway set and closes both (design 3.5: the
  boot-global `loop_check_gen` leaves 0, so every trace's first ADD takes the
  same arm), and reads `/proc/sys/fs/epoll/max_user_watches`; the harness
  fails the batch unless the value is the one the mirror assumes
  (`harness/linux.py EXPECTED_MAX_USER_WATCHES`, design 3.4).
- **Wire.** Opcodes 27 `epoll_create1` (`b = flags`), 28 `epoll_ctl`
  (`fd = epfd`, `newfd = fd`, `a = cmd`, `b = events`, `value = data`) and
  29 `epoll_wait` (`fd = epfd`, `a = maxevents`, `b = timeout`).

## Seccomp (amended 2026-10-12, seccomp stream W)

The amendment widens the domain; every earlier trace remains valid. The design
is `docs/2026-10-12-seccomp-design.md`, section 6. Five operations, no
descriptor arguments:

- **`{"op":"seccomp_install","via":"seccomp"|"prctl","flags":[...],"filter":[[code,jt,jf,k],...]|null}`**
  is `seccomp(SECCOMP_SET_MODE_FILTER, flags, &prog)` or
  `prctl(PR_SET_SECCOMP, mode, &prog)` with `prog = {len, filter}`. `flags`
  lists `SECCOMP_FILTER_FLAG_*` names (`tsync`, `log`, `spec_allow`,
  `new_listener`, `tsync_esrch`, `wait_killable_recv`) or raw bits 0–65535
  (the flag-mask arm); it is empty with `prctl`. Optional: `len` (0–65535)
  overrides the program's length for the length arms; `bad` (`fprog` or
  `insns`) passes an unmapped pointer for the `sock_fprog` or the
  instructions (the two `-EFAULT` arms); a `null` filter is the NULL
  instruction pointer; `mode` (0–255, `prctl` only, default 2) is
  `prctl_set_seccomp`'s mode argument. A program has 1–4096 instructions.
- **`{"op":"seccomp_probe","nr":n,"where":"self"|"child"}`** issues system
  call `nr` with six u64 `args` (optional, default zeros): in the trace
  process (`self`), or in a sandboxed child (`child`) that inherits the
  trace's filters, records its own coverage on descriptor 8, optionally sets
  strict mode first (`strict`: `seccomp` or `prctl`), and reports through a
  shared page. `nr` is in the probe set {102, 104, 107, 108, 1000, 335}, and
  60 (`exit`) for a strict child (design 6.2 rule 1: every other number is
  constant-allowed by a corpus filter's prologue, so the harness's own calls
  are cache hits). A self probe is invalid once an earlier install's filter
  may kill: a `RET|K` whose action is not `ALLOW`, `LOG`, `TRACE`, `ERRNO`
  or `TRAP`, a `RET|A`, or a `DIV|X` (the validator's conservative scan,
  `harness/trace.py filter_may_kill`; `MOD` is rejected at the install by
  `seccomp_check_filter`, so it is not scanned).
- **`{"op":"seccomp_prctl","cmd":"set_no_new_privs"|"get_no_new_privs"|"get_seccomp"}`**
  is `prctl(PR_SET_NO_NEW_PRIVS | PR_GET_NO_NEW_PRIVS | PR_GET_SECCOMP, arg2, arg3,
  arg4, arg5)` with the optional u64 arguments (default 0; the `-EINVAL`
  arms).
- **`{"op":"seccomp_capdrop"}`** is `capset` with `CAP_SYS_ADMIN` cleared from
  the effective, permitted and inheritable sets the process had at setup.
- **`{"op":"seccomp_query","cmd":"get_action_avail"|"get_notif_sizes"}`** is
  `seccomp(SECCOMP_GET_ACTION_AVAIL, flags, &action)` (`action`, a u32,
  required) or `seccomp(SECCOMP_GET_NOTIF_SIZES, flags, &sizes)`; `flags`
  optional, default 0.
- **Fixture.** A trace with a child probe declares `"seccomp_child": true`
  at the top level: descriptor 8 is then the child's KCOV descriptor
  (reserved, `rlimit_nofile` at least 9), never with a network fixture
  (8 and 9 are W8's injector and pin) and never with a steering schedule
  (the child loads none). Every trace process starts with a `SIGSYS`
  handler (`SA_SIGINFO`, no `SA_NODEFER`), `RLIMIT_CORE` 0, and its
  capability sets read for `seccomp_capdrop`.
- **Observation.** Every operation carries `ret` and `errno` as above; a
  child probe's `ret` is 0 (the parent's wait). `seccomp_probe` adds
  `sigsys`: `{"nr","data","arch"}` from the handler after a `TRAP`
  (`si_syscall`, `si_errno`, `si_arch`), else `null`; and `child`: `null`
  for a self probe, else an object with `strict_ret` (present exactly when
  `strict` was asked: the child's own strict call's result) and exactly one
  of `ret` (the child wrote its result and left normally), `exited`
  (the exit status of a child that left without writing) or `signal`
  (the signal that killed it: 31 `SIGSYS`, 9 `SIGKILL`). The child's
  coverage, choice records and comparison records reach the harness as
  `LEANUX_CCOVERAGE`, `LEANUX_CHIDDEN` and `LEANUX_CCMP` rows and are
  merged into the operation's rows after the parent's (stream `child`).
- **Wire.** Opcodes 30 `seccomp_install` (`a = via | mode << 8`, `b = flags
  | bad << 16` with `bad` 1 `fprog`, 2 `insns`, 3 null; `value = 1 << 32 |
  len` when `len` is given; payload the program, 8 bytes per instruction:
  `code` u16, `jt` u8, `jf` u8, `k` u32, little-endian), 31 `seccomp_probe`
  (`a = nr`, `b = where | strict << 8` with `strict` 1 `seccomp`, 2 `prctl`;
  payload the six u64 arguments), 32 `seccomp_prctl` (`a = cmd` 0–2; payload
  `arg2..arg5` as four u64), 33 `seccomp_capdrop`, 34 `seccomp_query`
  (`a = cmd` 0–1, `b = action`, `value = flags`). The `T` line's eighth
  field is 1 for a trace that declares `seccomp_child`.

## Fixture and isolation

Each trace starts in a fresh process in the pinned guest. Set the soft and hard
`RLIMIT_NOFILE` to 32. Descriptors 0–7 are occupied fixture descriptors; arrange
them before the trace and retain them throughout. Their precise roles (console,
input, KCOV, filler) are recorded by the runner. Operations cannot target them.
Descriptors 8–31 start free, and no eventfd objects exist. The model represents
0–7 as reserved slots and retains the bound and allocation cursor explicitly.

The parent may use process creation and pipes to run the fixture; those are not
trace operations. Child execution is sequential, with no injected signals or
external eventfd producers. Allocator-pressure failures and unexpected external
interference have separate experiment outcomes; neither counts as agreement.

(Amended 2026-10-06, A2.) A steered trace (`steer`, `expect`; the
choice-stream strategy) may declare `"domain_extension": "failslab"`: it forces
allocation failures at task-context `GFP_KERNEL`-class sites. The NULL is in
the allocator's output set (the OOM-victim path), but the forced trace as a
whole is not a possible Linux execution (a victim does not run its next
syscall), exactly as for the kernel's own `failslab` testing. The host refuses
such a failure without the marker, and the marker without such a failure
(`harness/steer.py`); the check report lists the traces that declare it.

## Output and comparison

The runner emits one object with exactly `version`, `id`, `observations`, and
`branches`. `observations` has exactly one entry per operation in input order:

```json
{"index":0,"ret":8,"errno":null,"bytes":"0500000000000000"}
```

`ret` is the signed raw Linux syscall result; failure is `-errno`. `errno` is null
on success and the positive error number on failure. If the C `syscall()` helper
normalizes a failure to -1, reconstruct the raw result from the captured errno
immediately. Successful reads include their first `min(ret, 64)` bytes as
lowercase hex (all of them for `ret ≤ 64`, so eventfd reads are unchanged);
every other operation or failed read has `bytes=""`. No comparison renames FD
numbers, ignores error state, or drops output bytes.

Per operation kind, an observation carries exactly these further fields
(amended 2026-10-06 for pipes):
- `pipe2`: `"fds": [r, w]` (the read end, then the write end) after success,
  `null` on failure;
- `read`: `"digest"`, the lowercase hex BLAKE2s-256 of all `ret` returned
  bytes when `ret > 0`, else `null`. The evaluator recomputes it from `bytes`
  for every read of at most 64 bytes;
- `epoll_wait`: `"digest"` likewise, over the `12·ret` bytes of the returned
  events (amended 2026-10-12, epoll);
- `write`: `"sigpipe"`, 1 if `SIGPIPE` is pending in the trace child after the
  call (it stays pending for the rest of the trace), else 0;
- `seccomp_probe`: `"sigsys"` and `"child"` (amended 2026-10-12, seccomp;
  the Seccomp section above).

The WireGuard operations' observations are specified by `evaluator/protocol.py`
and `harness/wg.py`, as are those operations' inputs (`harness/trace.py`); the
JSON schemas here cover the FD, eventfd and pipe operations only.

`branches` is an array of `{index,label}` records for mirror execution reporting.
It may be empty on the Linux side, where KCOV is retained separately per operation.
A declared value comparison adds `operands` (`[lhs, rhs]`, C values); at a
declared operand exclusion (`correspondence/kcov.json`, `operand_exclusions`)
it carries `operands_excluded`, the excluded operand's name, instead.
Labels are evidence to check against actual definitions and the correspondence
inventory, not a substitute for observations or source analysis.

The evaluator, not either runner, classifies agreement, semantic mismatch,
invalid input, unsupported input, environment/resource failure, timeout, crash,
missing coverage, and invalid output. Missing, repeated, out-of-order, extra,
oversized, or contradictory output is never a passing comparison. All input
traces must receive an evaluator result; unsupported or failed cases remain in
the report's denominator with their own counts.

## Internal guest transport

JSON is the persistent external format. A trusted host adapter may serialize
validated traces to a simpler guest format; it must preserve this contract.
The guest runner and host adapter must document that wire format together and
retain the exact serialized input in each experiment record. This does not
authorize schema or observation changes. Experimental syscall sequences execute
only inside QEMU; host checks are limited to compiler probes and model programs.
