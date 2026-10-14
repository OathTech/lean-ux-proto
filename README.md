# Lean-ux

Lean-ux is an executable model of selected Linux subsystems, written in Lean
and tested against a pinned Linux kernel in QEMU. It follows the kernel's data
structures and control flow while abstracting away C memory representation:
each choice point on a modelled path has a counterpart in the model, in the
same order, and the inputs the kernel draws from randomness, clocks, allocation
outcomes and scheduling are recorded at their source and replayed. The aim is
to make kernel behavior easier to inspect, experiment with, and reason about
formally.

This is a research prototype. Passing its tests is evidence of agreement on
the tested paths, not a proof of equivalence or a model of all of Linux.

## What's here

- **A Lean model:** file descriptors, eventfd, pipes and epoll; WireGuard
  configuration, handshakes, encrypted traffic, timers, device and peer
  lifecycle, routing and allocation-failure paths, with the packet queues and
  worker scheduling represented as the kernel keeps them. Single-task seccomp
  with classic-BPF translation and an interpreter service, landed on
  2026-10-13: the filter chain and its cache, the classic-BPF checker and
  translation, strict mode, and the sandboxed child probe; excluded: the
  listener protocol (`USER_NOTIF`, `NEW_LISTENER`), tracer-mediated `TRACE`,
  and threaded `TSYNC` synchronisation.
- **A Linux test runner:** executes operation traces in a single-CPU x86-64
  guest, using Linux 6.12.110 with coverage and input-recording patches. The
  approved build is named by an identity file; any other build is refused.
- **A differential checker:** compares observable results, instrumented branch
  decisions and comparison operands. Recorded randomness, clocks, allocation
  outcomes and dispatch order let the model replay the kernel's choices, so a
  run is a deterministic function of the trace and the records.
- **Test inputs:** handwritten cases, seeded generators, negative controls
  and sentinel mutants.
- **A proof tree:** theorems about the model, in `Leanux/Proofs/`, with their
  own build target and gate. The first result, replay freedom of WireGuard's
  receive counter window, is landed and current; six further WireGuard
  properties are chartered as a campaign.

Unsupported paths stop explicitly. The surrounding network stack and execution
environment are modeled only as needed by the covered paths; multi-CPU execution
and C's memory semantics are outside the current scope.

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

## Find your way around

| Location | Contents |
| --- | --- |
| [Leanux/](Leanux/) | Model: `FS/`, `WG/`, shared state in `Kernel/`, fixture and scheduling in `Env.lean` and `Env/` |
| [Leanux/Proofs/](Leanux/Proofs/) | Theorems about the model; the map and register are in [docs/proofs.md](docs/proofs.md) |
| [harness/](harness/README.md) | Guest runner, trace validation and packet construction |
| [evaluator/](evaluator/) | Trace generation and comparison with Linux |
| [corpus/](corpus/) | Example traces and regression cases |
| [correspondence/](correspondence/README.md) | How the model maps to C, and what the checks establish |
| [kernel/](kernel/) and [dependencies/](dependencies/) | Kernel patches, configurations, identities and dependency locks |
| [docs/](docs/README.md) | Decisions, designs, reviews and charters, indexed |

See the [trace format](contracts/trace-v1.md) to write inputs and
[offline usage](docs/offline-usage.md) to reuse a staged environment.
Development follows [AGENTS.md](AGENTS.md) and the
[worktree practices](docs/worktree-practices.md). Decisions and their
provenance are in [docs/decisions.md](docs/decisions.md); dated documents in
`docs/` are design and development history, rather than setup instructions.

## License

[GPL-2.0-only](LICENSE). Third-party dependencies retain their own licenses.
