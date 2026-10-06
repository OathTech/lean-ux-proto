# Linux experiment runner

Run from a checkout with its staged environment selected:

```
scripts/in-bundle python3 -m harness.linux INPUT.jsonl --out "$TASK_ARTIFACTS/run-001"
```

`INPUT.jsonl` contains one trace-v1 JSON object per line. `run_linux(traces,
outdir, timeout=120)` returns Linux observation objects in order. The output
directory must be empty and within `LEANUX_ARTIFACTS`; paths are never reused.
`LinuxRunError.kind` distinguishes build, guest, coverage, output, timeout, and
resource failures. These are experiment failures, not semantic disagreements.
Agreement is decided by `python3 -m evaluator.check`, which also builds and runs
the mirror; see the top-level README.

The runner builds only `guest.c`, then boots the accepted oracle kernel
`.artifacts/kernel-net-rcov` (`scripts/build-kernel` with
`LEANUX_KERNEL_PROFILE=net-rcov`: `kernel/config-x86_64-net` plus the
remote-coverage patch; `LEANUX_KERNEL_DIR` selects another build inside
the artifact roots) with one TCG CPU, 256 MiB memory, and no network device.
Traces with a WireGuard operation run in a fresh network namespace holding a
down WireGuard device `wg0`, with a generic-netlink socket at descriptor 7. A shared advisory lock reserves the one guest slot.
No experimental syscall sequence runs on the host. No kernel rebuild occurs.
Each call boots a fresh VM, and each trace runs in a fresh forked child. The
parent only reads the wire input and manages children; it owns no eventfd.

Each child verifies inherited console descriptors 0–2, closes the input-file
descriptor, opens KCOV at 3, fills 4–7 with `/dev/null`, and sets both
`RLIMIT_NOFILE` bounds to 32. Slots 8–31 start free. The fixture descriptors
remain open throughout. The child allocates valid 16-byte I/O buffers and uses
`syscall()` exactly once for each trace operation; failure is reconstructed
immediately from errno, with no retry. Flags and initial counts are unsigned
32-bit arguments; descriptor literals are sign-extended signed 32-bit values.
Failed producer references become -1; successful references retain their original
number even after closing or replacing that descriptor.

KCOV is enabled and reset immediately before each operation, and its count is
captured immediately afterwards, before disabling coverage. Empty or full
coverage fails the experiment. Per-operation records preserve the total PC
count and each unique address once, at its first execution, in execution order.

Each trace runs twice, in two fresh children:
- **PC mode** (`KCOV_TRACE_PC`) records coverage.
- **Comparison mode** (`KCOV_TRACE_CMP`) records every comparison's type, two
  operands and PC. Runs of identical records are printed once.

The comparison child's return values must equal the PC child's, or the run is
an environment failure (nondeterminism). Formatting, fixture setup, and parent
work are outside the captured intervals. Address randomization is disabled to
support source symbolization against the recorded `vmlinux`.

The run directory retains validated JSON input, exact wire input, observation
JSONL, per-operation coverage JSONL, fixture layout, full serial log, compiler
log, exact QEMU command, initramfs specification/image, and SHA-256 identities
of the runner, adapters, contracts, launcher, configured kernel, and guest files.
Unexpected EINTR, ENOMEM, ENFILE, or internal restart results are categorized as
environment failures. EMFILE is part of the intended descriptor-limit behavior.
Compiler and guest output together are capped at 16 MiB while being captured;
exceeding the cap ends the runner's process group and reports `output_limit`.
Use smaller guest batches when coverage would exceed this cap. Guest timeout is
120 seconds by default. Both timeout and output failures preserve captured logs.

## Guest wire format

The adapter is the sole wire producer. All persistent comparisons use JSON.
The ASCII wire begins with `LEANUX_WIRE_V2`, then a decimal trace count (1–4096),
then the dispatch set: `D N` and N hex function addresses (N ≥ 1 when a trace
uses the network fixture; `harness/linux.py` resolves them from `System.map`),
then `A 0` or `A 1`: whether the kernel writes the kind-303 timer arm records
(D3; `harness/linux.py` `ARM_RECORDS`), then the allocation set: `M FLAGS N`
and N hex `lo hi` ranges (A, docs/2026-10-05-a-alloc.md section 4.3; `M 0 0`
disarms, the default; flag 1 is the inventory mode, with N = 0 every
allocation in a recording context). Opcode 14 is `wg_advance`, its `a` the
ticks (D3, docs/2026-10-05-d3-timers.md).
Each trace begins `T ID N` for the validated identifier and operation count.
Exactly N operation lines follow, each with eight decimal fields:

```
opcode fd_kind fd_value new_kind new_value a b value
```

FD kinds are 0 for signed literal and 1 for earlier producer reference. Unused
FD fields are `0 -1`. Opcodes are 1 eventfd2, 2 dup, 3 dup3, 4 close, 5 read,
6 write, and 7 fcntl. `a` holds init/count/fcntl-command (otherwise 0); `b`
holds flags/fcntl-arg (otherwise 0). Fcntl commands are 1 GETFD, 2 SETFD,
3 GETFL. `value` is the uint64 write value, otherwise 0. There is one final
newline and no trailing data. Validation applies the full normative contract,
including cross-operation references, reserved descriptors, and NONBLOCK.

Guest serial records have separate `LEANUX_RESULT`, `LEANUX_COVERAGE`,
`LEANUX_FIXTURE`, and `LEANUX_ERROR` prefixes. Result objects implement the
observation contract exactly, with an empty Linux `branches` array. The adapter
rejects missing, repeated, out-of-order, contradictory, or malformed records.

The handwritten corpus contains 35 traces covering ordinary/semaphore counters,
sharing and independent objects, descriptor flags, replacement and reuse,
invalid inputs to the kernel that remain valid trace inputs, I/O lengths,
counter saturation, and descriptor exhaustion. Invalid trace syntax is checked
separately by `python3 -m unittest harness.test_trace`.

**Remote coverage.** For network traces, the per-trace child enables
`KCOV_REMOTE_ENABLE` with a common handle, then forks the process that runs
the trace. That process inherits the handle, and the skbs it allocates carry
it, so the patched kernel's receive paths (softirq and the handshake worker)
collect into a shared mapping. Per-task coverage stays enabled for the whole
trace, because `KCOV_DISABLE` clears the inherited handle. Each operation
resets both buffers, and its coverage row is the task PCs followed by the
remote ones.
