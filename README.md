# Lean-ux

> An executable Lean mirror of selected paths in a pinned, instrumented,
> single-CPU Linux configuration. Differential tests compare observations,
> declared branch witnesses and comparison operands, replaying recorded inputs
> and explicitly reconstructing some scheduling choices. Separate Lean theorems
> establish named properties of the mirror at stated boundaries. Neither the
> C-to-mirror correspondence nor general Linux or WireGuard security is proved.

Lean-ux is an executable model of selected Linux subsystems, written in Lean
and tested against a pinned Linux kernel in QEMU. It follows the kernel's data
structures and control flow while abstracting away C memory representation:
each choice point on a modelled path has a counterpart in the model, in the
same order, and the inputs the kernel draws from randomness, clocks, allocation
outcomes and scheduling are recorded at their source and replayed. The aim is
to make kernel behavior easier to inspect, experiment with, and reason about
formally.

This is a research prototype. Passing its tests is evidence of agreement on
the tested paths at the observation level described below, not a proof of
equivalence or a model of all of Linux. The [pre-release review](docs/2026-10-14-pre-release-review.md)
states the strongest criticisms of the evidence and what is being done about
each; the [scope table](#scope) below is its summary.

## What's here

- **A Lean model:** file descriptors, eventfd, pipes and epoll; WireGuard
  configuration, handshakes, encrypted traffic, timers, device and peer
  lifecycle, routing and allocation-failure paths, with the packet queues and
  worker scheduling represented as the kernel keeps them. Single-task seccomp
  with classic-BPF translation and an interpreter service, landed on
  2026-10-13: the filter chain and its cache, the classic-BPF checker and
  translation, strict mode, and the sandboxed child probe; excluded: the
  listener protocol (`USER_NOTIF`, `NEW_LISTENER`), tracer-mediated `TRACE`,
  and threaded `TSYNC` synchronisation. The eBPF interpreter is a service
  behind a contract (not a verified interpreter, verifier or JIT).
- **A Linux test runner:** executes operation traces in a single-CPU x86-64
  guest, using Linux 6.12.110 with coverage and input-recording patches. The
  approved build is named by an identity file; any other build is refused.
- **A differential checker:** compares observable results, instrumented branch
  decisions and comparison operands. Recorded randomness, clocks, allocation
  outcomes and dispatch order let the model replay the kernel's choices. Where
  the records do not determine a scheduling choice (a NAPI poll's placement,
  a worker's yield position), the checker reconstructs it from the records
  and the comparison evidence by a named rule and fails closed when the rule
  does not apply; the reconstructions are listed in
  [correspondence/](correspondence/README.md).
- **Test inputs:** handwritten cases, seeded generators filtered by the
  model's own domain (the candidate and selection counts are reported with
  every run, after the finding-3 fix on task/review-checker), negative
  controls and sentinel mutants.
- **A proof tree:** theorems about the model, in `Leanux/Proofs/`, with their
  own build target and gate. The first result, replay freedom of WireGuard's
  receive counter window, is landed; at this revision the
  [register](docs/proofs.md) records it as lagging since 247beec, with the
  repair on the proof campaign's branch pending its landing. Six further
  WireGuard properties are chartered as a campaign; each is a theorem about
  the model at a stated boundary, listed with its original claim and its
  counterexamples in the register's result table.
- **A tray of kernel findings:** [docs/upstream-tray/](docs/upstream-tray/INDEX.md),
  reports on kernel behaviour that might concern its maintainers, drafted for
  future filing; reports only, no patches.

Unsupported paths stop explicitly. The surrounding network stack and execution
environment are modeled only as needed by the covered paths.

## Scope

The model covers one configuration and a chosen set of compositions. The
exclusions that matter most, with their status:

| Exclusion | Status |
| --- | --- |
| Several CPUs; any architecture but x86-64; physical hardware (NIC, DMA, offload, real driver receive paths); production timing and performance | Excluded: the first target is one emulated CPU (`CONFIG_SMP=n`). SMP and hardware are future work, not a prerequisite of this prototype. |
| More than one WireGuard device per guest | Deferred: W13 (a device map, receive demultiplexing by socket, two NAPIs in one softirq), scoped in the [decision census](docs/2026-10-13-decision-census.md) §7. |
| A receive racing a previously queued handshake worker, which includes ordinary simultaneous initiation | Excluded by the pending-handshake rule (`requireNotPending`), an explicit stop. Closed in the review-fix integration (2026-10-14): the stop is retired, the records determine the order (`docs/2026-10-11-dispatch-order.md`, last section); three batch traces whose two guest children disagree run to run are held outside the suites. |
| Several peers' NAPI polls in one softirq; a full NAPI budget | Excluded, explicit stops; deferred with W13. |
| Device deletion with a dump pending or work queued | Excluded: the guest refuses it; the model's matching refusal is the finding-6 fix on task/review-timer. The cursor's ownership across device lifetimes is deferred. |
| Blocking file-descriptor operations, epoll waits with a timeout, more than one task in the FD slice | Excluded: the slice is nonblocking, zero-timeout and single-task; blocking waits need a sleep record (epoll tier 2, deferred). |
| IPv6 rate limiting (`/64` keys) and the rate limiter's periodic GC | Closed in the review-fix integration (2026-10-14): the `/64` rate-limit path is modelled with its traces; the limiter's periodic GC stays excluded with its reason in the E design. |
| Seccomp user notification, thread synchronisation with real threads, tracer-mediated TRACE, instruction-pointer loads, policy errno values 4, 12 and 23 | Excluded: a second thread, a tracer or an unrecorded input. The single-thread TSYNC no-op, the instruction-pointer record (kind 312) and the errno provenance landed in the review-fix integration (2026-10-14); the protocols stay excluded. |
| Filter release and exit effects, and anything after a finite wait | Excluded: outside the recorded windows; a trace observes prefixes. |
| A second compiler or optimisation level | In progress: the [compiler experiment](docs/2026-10-13-compiler-experiment.md)'s size-optimised image was refused by three build-bound layers; the reader's second phase is a named follow-on. Declarations follow the -O2 build. |

A gap is excluded only for a recorded reason; "the fixture does not generate
it" is a status, not a justification, and the census lists every unexercised
decision outcome with its reason or its absence.

## Run it

Follow [setup and first run](REPRODUCING.md) first. You need a Linux x86-64 host
(Ubuntu 24.04 is the reference environment) and the pinned tools. Dependencies
are downloaded into the checkout; they are not included in Git. The guide
includes a model-only example before building the test kernel.

Once set up, run these from your worktree, with `LEANUX_KERNEL_DIR` pointing
to the approved kernel build:

```sh
# One small end-to-end test
scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close

# The handwritten WireGuard cases
scripts/in-bundle python3 -m evaluator.check --suite wireguard

# All default suites, including generated cases; allow roughly an hour
scripts/in-bundle python3 -m evaluator.check

# The proof tree: build and axiom check
scripts/in-bundle scripts/proof-gate
```

The checker builds the model, boots the guest, and writes
`.artifacts/check/<timestamp>/report.json`. Success means exit status 0 and
`"status": "pass"`; mismatches and infrastructure failures both fail the run.
The proof gate prints the axioms of every proved statement and fails on any
beyond Lean's three standard ones.

## Trusted boundary and target configuration

The oracle is a configured, patched build of Linux 6.12.110, not a stock
kernel. What the identity gate pins, and what it does not show:

- **Record-only hooks** (`kernel/patches/choice-stream.patch`): coverage
  sections for workers and timers, and records of the hidden inputs at their
  sources (random bytes, clock reads, allocation outcomes, dispatch order,
  epoll's tree order, seccomp's translated program, the end-of-wait jiffies).
  They add no line to an anchored source file.
- **Value steering** on the control twin: allocation failures and task
  instances forced at approved sites, so that error arms can be exercised.
- **Virtual time:** a jiffies advance the trace can request, so that timers
  fire without waiting.
- **Observation decoding:** the guest prints observations and the harness
  decodes them; the guest and the decoder are trusted implementation.
- **Service cuts:** the cryptographic primitives, packet construction and
  decoding, and the eBPF interpreter are used as services behind contracts,
  not mirrored.

Recording changes timing and allocation pressure; the identity gate shows
which build ran, not that the hooks preserve stock behaviour. A smoke sample
of unsteered observations against a matched stock build is a named follow-on
of the review. The configuration (`kernel/config-x86_64-net-choice`):
`CONFIG_SMP=n`, `CONFIG_PREEMPT_NONE=y`, `CONFIG_HZ=250`, `CONFIG_BPF_JIT=n`,
`CONFIG_SECCOMP=y`, no user namespaces, no netfilter, KCOV with comparison
tracing. The guest (`harness/linux.py`): QEMU TCG, single-threaded,
`pc-i440fx-8.2`, `qemu64`, one CPU, 256 MiB, serial console, no NIC; all
traffic is in-guest over loopback. Multi-CPU execution, C's memory semantics,
constant time and the physical erasure of secrets are outside the model.

## Find your way around

| Location | Contents |
| --- | --- |
| [Leanux/](Leanux/) | Model: `FS/`, `WG/`, `Seccomp/`, shared state in `Kernel/`, fixture and scheduling in `Env.lean` and `Env/` |
| [Leanux/Proofs/](Leanux/Proofs/) | Theorems about the model; the map, the register and the result table are in [docs/proofs.md](docs/proofs.md) |
| [harness/](harness/README.md) | Guest runner, trace validation and packet construction |
| [evaluator/](evaluator/) | Trace generation and comparison with Linux |
| [corpus/](corpus/) | Example traces and regression cases |
| [correspondence/](correspondence/README.md) | How the model maps to C, and what the checks establish and do not |
| [kernel/](kernel/) and [dependencies/](dependencies/) | Kernel patches, configurations, identities and dependency locks |
| [docs/](docs/README.md) | Decisions, designs, audits, reviews and charters, indexed |

See the [trace format](contracts/trace-v1.md) to write inputs and
[offline usage](docs/offline-usage.md) to reuse a staged environment.
Development follows [AGENTS.md](AGENTS.md) and the
[worktree practices](docs/worktree-practices.md). Decisions and their
provenance are in [docs/decisions.md](docs/decisions.md); dated documents in
`docs/` are design and development history, rather than setup instructions.

## License

[GPL-2.0-only](LICENSE). Third-party dependencies retain their own licenses.
