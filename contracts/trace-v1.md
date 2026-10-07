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
earlier operation index whose operation is `eventfd2`, `dup`, or `dup3`. A
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
- `write`: `"sigpipe"`, 1 if `SIGPIPE` is pending in the trace child after the
  call (it stays pending for the rest of the trace), else 0.

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
