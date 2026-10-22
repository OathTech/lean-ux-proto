# Lean-ux

> **Health warning.** This is an agent-built research prototype: its model,
> tests, proofs and documents were written largely by AI coding agents,
> directed and reviewed by the maintainer. It is published for research
> purposes only. It is not a verified implementation, not a security tool and
> not intended for use in any product or deployment, and nothing here is a
> claim about the correctness or security of Linux or WireGuard. Read the
> [scope](#scope) and the [register](docs/proofs.md#results) before
> relying on any statement in this repository.

Lean-ux is an executable Lean model of selected Linux subsystems, tested
against a pinned, instrumented Linux 6.12.110 kernel in QEMU. The model follows
the kernel's data structures and control flow while leaving out C memory
representation. We call this a *mirror*: it is intended to make those paths
easier to inspect, test and reason about.

The repository combines differential tests, proofs about the Lean model, and
a separate experiment relating selected compiled functions to that model.
These provide different kinds of evidence. There is **no general proof that
the mirror implements Linux faithfully**, and the model proofs do not establish
the correctness or security of Linux or WireGuard.

## What is modeled

| Area | Included paths | Main limits |
| --- | --- | --- |
| File descriptors | Descriptor lifetime and aliasing, eventfd, pipes and epoll | One task; nonblocking operations and zero-timeout epoll waits |
| WireGuard | Configuration, Noise handshakes, encrypted traffic, queues and workers, timers, peer/device lifecycle, cookies, rate limiting and selected allocation failures | One WireGuard device; selected single-CPU schedules and network fixtures |
| Routing | The IPv4 FIB trie and routing behavior needed by the WireGuard paths | Not a general model of the Linux network stack |
| Seccomp | Single-task filter chains and cache, classic-BPF checking and translation, strict mode and a sandboxed child probe | No user-notification protocol, tracer-mediated TRACE or synchronization of real threads; the eBPF interpreter is a service, not a verified interpreter or JIT |

Unsupported paths stop explicitly. The execution environment is part of the
model's scope: fixtures, scheduling rules and observation windows constrain
which traces it can accept.

## What the evidence supports

**Differential tests** run operation traces in Linux and the mirror, comparing
results such as return values, packets and counters, plus declared branch
witnesses and comparison operands from kernel instrumentation. Hidden inputs
such as random draws, clocks and allocation outcomes are recorded and replayed.
Some scheduling choices are reconstructed by explicit rules, including rules
that use comparison evidence to select a placement. A pass is evidence of
agreement for the selected traces and observations, not an equivalence proof.
Generated tests are filtered by the model's own supported domain; reports
include candidate, selection and rejection counts.
[How the comparison works and where it is incomplete](correspondence/README.md).

**Lean proofs** establish named properties of the mirror. The three WireGuard
campaigns cover the following areas; this summary does not replace their
[claim register](docs/proofs.md#results), which names the statements, premises
and mirror revision for each result.

The earlier [receive replay-window result (S1–S3)](docs/2026-10-13-spike-window.md)
establishes an exact acceptance history with no repeated counter in one
allocation lifetime, refines the validator to a Lean specification of the
receive rule, and proves that unrelated keypairs' windows are preserved under
the stated lifetime-aware invariant. Identifying that specification with the
C rule remains a source-correspondence claim.

| Campaign | Results and boundaries |
| --- | --- |
| [1: receive and lifetime](docs/2026-10-13-proof-campaign.md) | Anti-replay uniqueness, lifetime safety for recorded committed accesses (failed lookups are outside the statement), routing authorization and ingress conservation; local key-lifetime and cookie-gate contracts. Chronological delivery order after receive aggregation (GRO) and some proposed lifetime/retry claims were refuted. |
| [2: handshake and configuration](docs/2026-10-14-proof-campaign-2.md) | Noise state-machine contracts; session-index uniqueness at normal initialized endpoints (H2); endpoint-roaming provenance; one-directional readback for four peer fields, under an entry invariant not derived at initialized endpoints (H4); finite operation evaluation and guarded timer discipline. Accepted operation boundaries have no pending work units in either record mode; this does not imply empty packet queues, eventual delivery or absence of scheduled NAPI polls. |
| [3: transmit and security-related properties](docs/2026-10-18-proof-campaign-3.md) | Per-allocation nonce uniqueness (keyed by key allocation, not by key material), transmit accounting at declared points, scoped authenticated-effect/silence claims and reference-aware retirement. Separate proofs connect packets to peers, keys and endpoints; they are not yet combined into one transmit-authorization result. Handshake replay resistance (T4) and responder confirmation (T5) still depend on named premises that have not been constructed. |

These theorems concern the Lean definitions and their stated observations.
In particular, **R2's lifetime safety does not establish absence of invalid
dereferences**. The [lifetime fault probe](docs/2026-10-21-lifetime-fault-probe.md)
shows that its allocation invariant alone does not exclude peer/keypair
lookup faults; the initialized fault-exclusion goal remains open.
Completeness of the proof-side event logs (journals) rests on construction and review,
not a general theorem that every relevant event is recorded. Cryptographic
primitives are treated as services; the campaigns do not prove cryptographic
security. Proofs have their own build and axiom checks, separate from the model.

**The [binary refinement experiment](binary/README.md)** relates selected
compiled WireGuard functions to the mirror under Kraken's x86-64 semantics
and explicit environment, memory and service premises. It includes an index
lookup theorem and sequential paired-execution results. The allowed-IPs
mutation experiment ended with component proofs and tests, with no newly
completed function. There is no whole-subsystem or concurrent-kernel refinement.
Proofs build from committed image terms; replaying kernel-image tests also
requires a saved ELF that cannot currently be reproduced from the clone alone.

**[Kernel report drafts](docs/upstream-tray/INDEX.md)** collect observations and
questions for possible upstream discussion. Some have kernel trace evidence;
others concern source-level races outside this single-CPU fixture. They are
not confirmed vulnerability reports or evidence that the whole kernel was checked.

## Scope

The principal limits are:

- One emulated x86-64 CPU, with no physical NIC, DMA, driver receive path or
  hardware offload. SMP, C's memory semantics, timing channels, constant time,
  physical key erasure and production performance are outside the model.
- One WireGuard device. Several peers' NAPI polls in one softirq, a full-budget
  NAPI repoll, and device deletion with a dump or work pending remain outside
  the supported domain. Recording dispatch order removed an older blanket
  exclusion on receiving while handshake work is queued; it did not make all
  schedules supported.
- Only the surrounding IP-stack paths needed by the fixture. IPv6 rate
  limiting is included, but the rate limiter's periodic garbage collection
  is excluded. Blocking FD operations, real seccomp thread synchronization,
  user notification and tracer protocols are also excluded.
- Finite recorded windows. A successful trace does not describe all later
  work, teardown effects or delivery. An unsupported continuation is a stop,
  not a successful model of that behavior.

The test oracle is a patched kernel, not a stock build. Its hooks record
inputs and coverage; it also supports controlled input steering and virtual
time advances. Instrumentation can affect timing and allocation pressure.
The identity check establishes which build ran, not that the patches preserve
stock-kernel behavior. The checked-in
[configuration](kernel/config-x86_64-net-choice) uses `CONFIG_SMP=n`,
`CONFIG_PREEMPT_NONE=y`, `CONFIG_HZ=250` and `CONFIG_BPF_JIT=n`; the guest uses
QEMU TCG, one CPU, 256 MiB RAM and in-guest loopback traffic.

The [scope review](docs/2026-10-20-fresh-eyes-scope-review.md) assesses the gap
between these results and verification of real Linux. The
[decision census](docs/2026-10-13-decision-census.md) and
[pre-release review](docs/2026-10-14-pre-release-review.md) explain coverage
limits and earlier findings at their recorded revisions; they are not a
current count of all Linux choices.

## Run it

Start with [setup and first run](REPRODUCING.md). It gives a model-only example
before the kernel build, then a small end-to-end comparison. You need Linux
x86-64 and the pinned tools; downloaded dependencies are not included in Git.
The separate binary package has additional prerequisites.

After setup, from a worktree with `LEANUX_KERNEL_DIR` set to the matching build:

```sh
# One small comparison
scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close

# Handwritten WireGuard cases
scripts/in-bundle python3 -m evaluator.check --suite wireguard

# All default suites; allow roughly an hour, depending on the host
scripts/in-bundle python3 -m evaluator.check
```

A successful check exits 0 and writes `"status": "pass"` to
`.artifacts/check/<timestamp>/report.json`. Inspect the reported selection and
coverage gaps along with the verdict. Mismatches and infrastructure failures
both fail the run. The setup guide also covers the separate proof checks.

## Find your way around

| Location | Contents |
| --- | --- |
| [Leanux/](Leanux/) | Executable model; environment and scheduling in `Env.lean` and `Env/` |
| [docs/proofs.md](docs/proofs.md) | Mirror proof register, assumptions, revision pins and tree map |
| [binary/](binary/README.md) | Separate binary refinement experiment and its trust boundary |
| [harness/](harness/README.md), [evaluator/](evaluator/) | Linux runner, trace generation and differential comparison |
| [corpus/](corpus/) | Example and regression traces; see the [trace contract](contracts/trace-v1.md) |
| [correspondence/](correspondence/README.md) | Source mappings, instrumentation and limits of comparison |
| [kernel/](kernel/), [dependencies/](dependencies/) | Configurations, patches, identities and dependency locks |
| [docs/](docs/README.md) | Reading guide, designs, reviews and historical reports |

Development follows [AGENTS.md](AGENTS.md) and the
[worktree practices](docs/worktree-practices.md). Decisions and their provenance
are in [docs/decisions.md](docs/decisions.md).

## License

[GPL-2.0-only](LICENSE). Third-party dependencies retain their own licenses.
