# Setup and first run

This guide builds the Lean model and runs it against the pinned Linux guest.
Start at the root of a clone, in a path without spaces. Downloads are needed
only for staging; builds and tests then run locally.

## 1. Prepare the environment

Use Linux x86-64 with glibc 2.39 or newer; Ubuntu 24.04 is the reference host.
The bootstrap needs Python 3.12+ at `/usr/bin/python3`, `/bin/sh`, Git, curl,
GNU tar, zstd and `dpkg-deb`. Lean, GCC, QEMU and the kernel build tools come
from the pinned bundle. KVM and root access are not needed to run the tests.
Budget roughly 15 GB for dependencies and builds, plus space for test output.

**The build currently also requires `capped`, an external memory-limit
wrapper that is not included in this repository.** Obtain it from the project
maintainers and use a session with working cgroup v2 delegation. The scripts
expect `/usr/local/bin/capped`; if it lives elsewhere, set `LEANUX_CAPPED` to
its absolute path. The commands below use that variable. Test it first:

```sh
export LEANUX_CAPPED=/usr/local/bin/capped
"$LEANUX_CAPPED" -- true
```

Stage the locked tools and Linux source in the main checkout:

```sh
python3 scripts/stage-resources.py packages
python3 scripts/stage-resources.py sources --sources linux
python3 scripts/restore-toolchains.py --only lean
```

These download from the Ubuntu snapshot service, kernel.org and GitHub, verify
the locked SHA-256 hashes, and extract into `.tools/` and `.deps/`. They do not
install system packages. Lean is pinned to 4.33.1. Go, syzkaller, Firecracker
and the Lean MCP helper are optional and not needed here.

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
"$LEANUX_CAPPED" -- scripts/in-bundle lake build leanux-model
"$LEANUX_CAPPED" -- scripts/in-bundle .lake/build/bin/leanux-model <<'EOF'
{"version":1,"id":"first_eventfd","ops":[{"op":"eventfd2","init":5,"flags":2048},{"op":"read","fd":{"ref":0},"count":8}]}
EOF
```

The model reads one JSON trace per line and emits one result per trace. This
example creates a nonblocking eventfd at descriptor 8 and reads its initial
value, 5; the read bytes are `0500000000000000`. It needs no guest kernel.
Build the explicit `leanux-model` target: plain `lake build` builds only the
library.

After building, run the unit tests, including recorded model replays:

```sh
"$LEANUX_CAPPED" -- scripts/in-bundle python3 -B -m unittest \
  evaluator.test_evaluation evaluator.test_model_replay \
  harness.test_trace harness.test_wg harness.test_noise \
  harness.test_d1_keys harness.test_d1_keepalive harness.test_linux
```

## 3. Build the Linux test kernel

```sh
export LEANUX_KERNEL_DIR="$PWD/.artifacts/kernel-net-choice"
LEANUX_KERNEL_PROFILE=net-choice LEANUX_KERNEL_BUILD="$LEANUX_KERNEL_DIR" \
  "$LEANUX_CAPPED" -- scripts/in-bundle scripts/build-kernel
```

This extracts a private copy of Linux 6.12.110, applies the pinned
`choice-stream.patch`, and builds the `net-choice` profile with four jobs by
default (`LEANUX_JOBS` overrides this). It also writes the generated
configuration to `kernel/config-x86_64-net-choice`; check `git diff` afterwards.

Every check and guest boot verifies the build against
[`kernel/identity-x86_64-net-choice.txt`](kernel/identity-x86_64-net-choice.txt).
A stock kernel or an older project kernel cannot substitute for it. To reuse
an existing matching build, skip the build command and set
`LEANUX_KERNEL_DIR` to its absolute path inside a checkout's `.artifacts/`
(the current worktree or its main checkout).

## 4. Compare with Linux

Keep `LEANUX_KERNEL_DIR` exported in the shell where you run:

```sh
# Small smoke test
"$LEANUX_CAPPED" -- scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close

# Handwritten WireGuard suite
"$LEANUX_CAPPED" -- scripts/in-bundle python3 -m evaluator.check --suite wireguard

# All default suites; allow roughly an hour, depending on host load
"$LEANUX_CAPPED" -- scripts/in-bundle python3 -m evaluator.check
```

The checker builds the model automatically. `--no-build` reuses a build only
if it is up to date. `--suite` accepts a comma-separated list: `handwritten`,
`critic`, `wireguard`, `alloc`, `generated`, `wireguard-generated`, `pipes`,
`pipes-generated`. Generated cases use a fixed default seed. Use `--trace ID`
with the relevant suite to replay one case.

A passing run exits 0 and writes `"status": "pass"` in
`.artifacts/check/<timestamp>/report.json`, with every selected trace counted
as `agreement`. Counts depend on the revision and selection; old stage reports
are not current expected totals. The report also records failures, filtered
candidates, known coverage gaps and any infrastructure retries. Detailed guest
and model output lives beside it. These outputs are disposable; remove your
run directories when finished.

If a run fails, inspect `aborted` and `failures` in the report, then the named
build or guest log. A missing wrapper, kernel identity mismatch, timeout,
`KILLED` banner or model error is a failed run. Keep `LEANUX_QEMU_SLOTS` at its
default of 3 on shared hosts; heavy contention can exhaust timing budgets.

Negative controls and sentinel mutants are separate developer checks described
in [AGENTS.md](AGENTS.md). They are not part of this first-run sequence.
For an existing offline bundle, see [offline usage](docs/offline-usage.md).
