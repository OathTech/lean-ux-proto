# Setup and first run

This guide starts with a model-only example, then compares a trace with the
pinned Linux guest. Read the [health warning and scope](README.md) first.
Start at the root of a clone, in a path without spaces. Downloads are needed
for staging; the mirror builds and tests then run locally.

## 1. Prepare the environment

Use Linux x86-64 with glibc 2.39 or newer; Ubuntu 24.04 is the reference host.
The bootstrap needs Python 3.12+ at `/usr/bin/python3`, `/bin/sh`, Git, curl,
GNU tar, zstd and `dpkg-deb`. Lean, GCC, QEMU and the kernel build tools come
from the pinned bundle. KVM and root access are not needed to run the tests.
Allow space for the tool bundle, Linux sources, a kernel build and test
output; full proof builds and the optional binary package need additional
space beyond the first run.

On shared devboxes, wrap heavy commands with the installed `capped` tool.
The following shell helper also works on ordinary hosts where it is absent:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
```

The checker and kernel builder also use the box wrapper internally when
available. An absent optional wrapper is a notice, not a failed check; an
explicitly configured wrapper that cannot run is an error.

Lean comes from [elan](https://github.com/leanprover/elan), the Lean
toolchain manager. Install elan, then install the toolchain this checkout
pins in `lean-toolchain` (4.35.0):

```sh
elan toolchain install "$(cat lean-toolchain)"
```

`scripts/in-bundle` locates that toolchain through elan and checks that its
`lean --version` reports the pinned version; it never builds with an
unversioned `lean` from `PATH`, and a checkout on another pin needs that
toolchain installed the same way. (The project's shared devboxes keep a staged
snapshot under `.tools/`, which the launcher uses first; see
[offline usage](docs/offline-usage.md).)

Stage the locked tools and Linux source in the main checkout:

```sh
python3 scripts/stage-resources.py packages
python3 scripts/stage-resources.py sources --sources linux
```

These download from the Ubuntu snapshot service and kernel.org, verify the
locked SHA-256 hashes, and extract into `.tools/` and `.deps/`. They do not
install system packages. Go, syzkaller, Firecracker and the Lean MCP helper
are optional and not needed here.

The [binary refinement package](binary/README.md) is optional and has a
separate setup. In particular, its Python entry points need pyelftools in
the interpreter used to launch them, and its image-execution tests need a
specific saved kernel ELF. The mirror setup below does not provide that artifact.

Create a worktree for builds and experiments:

```sh
git worktree add .worktrees/first-run -b task/first-run main
cd .worktrees/first-run
scripts/in-bundle lean --version
```

`scripts/in-bundle` uses the main checkout's tools and sources, with build
outputs and caches private to this worktree. It selects tools; it is not a
sandbox. A sandbox such as nono is optional.

## 2. Build and try the model

```sh
cap scripts/in-bundle lake build leanux-model leanux-fixed-width-tests
scripts/in-bundle .lake/build/bin/leanux-model <<'EOF'
{"version":1,"id":"first_eventfd","ops":[{"op":"eventfd2","init":5,"flags":2048},{"op":"read","fd":{"ref":0},"count":8}]}
EOF
```

The model reads one JSON trace per line and emits one result per trace. This
example creates a nonblocking eventfd at descriptor 8 and reads its initial
value, 5; the read bytes are `0500000000000000`. It needs no guest kernel.
Build the explicit `leanux-model` target: plain `lake build` builds only the
library. The second target supplies the fixed-width counter witness required by
`evaluator.test_model_replay` (`tests/FixedWidthTests.lean`).

After building, run the unit tests, including recorded model replays:

```sh
cap scripts/in-bundle python3 -B -m unittest \
  evaluator.test_evaluation evaluator.test_model_replay \
  harness.test_trace harness.test_wg harness.test_linux
```

This is the five-module fast tier named in [AGENTS.md](AGENTS.md).
Additional Noise and keepalive vectors are available in `harness.test_noise`
and `harness.test_d1_keepalive`.

Known failure ([overseer follow-up](docs/2026-10-22-setup-findings.md)): the
optional `harness.test_d1_keys` test still constructs the
pre-split Lean state and fails to compile (ambiguous `M` and obsolete `World`
fields). The broader command previously listed here therefore fails. Repairing
that test is separate from the passing fast tier; do not count it as validated.

## 3. Build the Linux test kernel

```sh
export LEANUX_KERNEL_DIR="$PWD/.artifacts/kernel-net-choice"
LEANUX_KERNEL_PROFILE=net-choice LEANUX_KERNEL_BUILD="$LEANUX_KERNEL_DIR" \
  cap scripts/in-bundle scripts/build-kernel
```

This extracts a private copy of Linux 6.12.110, applies the pinned
`choice-stream.patch` and builds the `net-choice` profile. The patch records
coverage, hidden inputs and dispatches, and provides steering and virtual-time
facilities. The builder uses four jobs by default (`LEANUX_JOBS` overrides
this). It also writes the generated configuration to
`kernel/config-x86_64-net-choice`; inspect `git diff` afterwards.

Every normal check and guest boot compares the build's identity with
[`kernel/identity-x86_64-net-choice.txt`](kernel/identity-x86_64-net-choice.txt).
That file is the authority; a directory name is only a convenience. A stock
kernel or an older project build cannot substitute for the pinned oracle.
The identity describes the configured, instrumented build, not an assertion
that it behaves exactly like stock Linux.

To reuse an existing matching build, skip the build command and set
`LEANUX_KERNEL_DIR` to its absolute path inside a checkout's `.artifacts/`
(the current worktree or its main checkout). The negative controls also use
profile `net-choice-actl`, with its separate identity file; the first run
does not need it. Explicit alternative identities are for separately labeled
experiments and controls, not a way to pass the normal oracle check.

## 4. Compare with Linux

Keep `LEANUX_KERNEL_DIR` exported in the shell where you run:

```sh
# Small smoke test
cap scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close

# Handwritten WireGuard suite
cap scripts/in-bundle python3 -m evaluator.check --suite wireguard

# All default suites; allow roughly an hour, depending on host load
cap scripts/in-bundle python3 -m evaluator.check
```

The checker builds the model automatically. `--no-build` reuses a build only
if it is up to date. `--suite` accepts a comma-separated list: `handwritten`,
`critic`, `wireguard`, `alloc`, `generated`, `wireguard-generated`, `pipes`,
`pipes-generated`, `routing`, `epoll`, `epoll-generated`, `seccomp`, `seccomp-generated`,
and `w7-tier` (the full-ring tier, outside the default list). Generated cases
use a fixed default seed; `--generated-count`, `--wireguard-count`,
`--pipes-count`, `--epoll-count` and `--seccomp-count` set their sizes. The
generated suites are filtered by the model's own domain before selection;
the report carries the candidate and selected counts with the rejection
reasons. Use `--trace ID` with the relevant suite to replay one case.
Use `--help` for the complete current option list.

A passing run exits 0 and writes `"status": "pass"` in
`.artifacts/check/<timestamp>/report.json`, with every selected trace counted
as `agreement`. Counts depend on the revision and selection; old stage reports
are not current expected totals. The report also records failures, filtered
candidates, known coverage gaps and any infrastructure retries. Detailed guest
and model output lives beside it. These outputs are disposable; remove your
run directories when finished.

If a run fails, inspect `aborted` and `failures` in the report, then the named
build or guest log. A kernel identity mismatch, timeout, `KILLED` banner or
model error is a failed run. `LEANUX_QEMU_SLOTS` bounds the guests running at
once across every checkout, through lock files in the main checkout's
`.artifacts/runs/`; the default is 16. Set a lower value on a smaller or busier
machine. Heavy contention can exhaust timing budgets.

Negative controls and sentinel mutants are separate developer checks described
in [AGENTS.md](AGENTS.md). They are not part of this first-run sequence.
For an existing offline bundle, see [offline usage](docs/offline-usage.md).

## 5. Build and check the proofs

The proof tree `Leanux/Proofs/` is a separate target, outside the model's
default build. Its gate needs no guest and builds the target itself:

```sh
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle scripts/proof-counterexamples
```

The first command builds `LeanuxProofs`, checks the axioms of declarations
in every module directly imported by `Leanux/Proofs.lean`, scans for
admissions and unsafe constructs, and checks the proof tree's separation
from the executable model. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted axioms. It ends with `proof gate: PASS` and exit 0.
A build alone does not run all these checks. The second command replays the
published witness and counterexample recipes through the Lean interpreter;
it is a separate diagnostic check, not part of the gate.

A passing gate checks the formal statements and their dependencies, not
whether their assumptions describe Linux. Read the
[claim register](docs/proofs.md#results) for each result's premises and mirror
pin. Campaigns 2 and 3 include scoped and conditional claims as well as
counterexamples; the number of theorems is not a measure of kernel coverage.
