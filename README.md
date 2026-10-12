# Lean-ux

Lean-ux is an executable model of selected Linux subsystems, written in Lean
and tested against a pinned Linux kernel in QEMU. It follows the kernel's data
structures and control flow while abstracting away C memory representation.
The aim is to make kernel behavior easier to inspect, experiment with, and
eventually reason about formally.

This is a research prototype. Passing its tests is evidence of agreement on
the tested paths, not a proof of equivalence or a model of all of Linux.

## What's here

- **A Lean model:** file descriptors, eventfd and pipes; WireGuard configuration,
  handshakes, encrypted traffic, timers, device and peer lifecycle, and selected
  routing and allocation-failure paths.
- **A Linux test runner:** executes operation traces in a single-CPU x86-64
  guest, using Linux 6.12.110 with coverage and input-recording patches.
- **A differential checker:** compares observable results, instrumented branch
  decisions and comparison operands. Recorded randomness, clocks and dispatch
  events let the model replay the kernel's choices.
- **Test inputs:** handwritten cases, seeded generators, negative controls
  and mutation checks.

Coverage is still growing, with single-CPU WireGuard as the main target.
Unsupported paths stop explicitly. The surrounding network stack and execution
environment are modeled only as needed by those paths; multi-CPU execution
and C's memory semantics are outside the current scope.

## Run it

Follow [setup and first run](REPRODUCING.md) first. You need a Linux x86-64 host
(Ubuntu 24.04 is the reference environment), the pinned tools, and the external
`capped` memory-limit wrapper. Dependencies are downloaded into the checkout;
they are not included in Git. The guide includes a model-only example before
building the test kernel.

Once set up, run these from your worktree, with `LEANUX_KERNEL_DIR` pointing
to the matching kernel build:

```sh
# One small end-to-end test
capped -- scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close

# The handwritten WireGuard cases
capped -- scripts/in-bundle python3 -m evaluator.check --suite wireguard

# All default suites, including generated cases; allow roughly an hour
capped -- scripts/in-bundle python3 -m evaluator.check
```

The checker builds the model, boots the guest, and writes
`.artifacts/check/<timestamp>/report.json`. Success means exit status 0 and
`"status": "pass"`; mismatches and infrastructure failures both fail the run.

## Find your way around

| Location | Contents |
| --- | --- |
| [Leanux/](Leanux/) | Model: `FS/`, `WG/`, shared state in `Kernel/`, fixture and scheduling in `Env.lean` and `Env/` |
| [harness/](harness/README.md) | Guest runner, trace validation and packet construction |
| [evaluator/](evaluator/) | Trace generation and comparison with Linux |
| [corpus/](corpus/) | Example traces and regression cases |
| [correspondence/](correspondence/README.md) | How the model maps to C, and what the checks establish |
| [kernel/](kernel/) and [dependencies/](dependencies/) | Kernel patches, configurations, identities and dependency locks |

See the [trace format](contracts/trace-v1.md) to write inputs and
[offline usage](docs/offline-usage.md) to reuse a staged environment.
Development follows [AGENTS.md](AGENTS.md) and the
[worktree practices](docs/worktree-practices.md). Dated documents in `docs/`
are design and development history, rather than setup instructions.

## License

[GPL-2.0-only](LICENSE). Third-party dependencies retain their own licenses.
