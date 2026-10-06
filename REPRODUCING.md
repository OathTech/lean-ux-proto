# Reproducing the results from a clone

This takes a fresh clone to a passing `evaluator.check`, with the same kernel,
toolchain and results as the recorded evidence. Every download is pinned by
sha256. Expect about 2 GB of downloads, a few minutes of builds, and about
1.5 hours for the full check.

**Host.** Linux x86-64, glibc 2.39 or newer, `/bin/sh`, Python 3.9+, `curl`,
`tar`, `zstd`, `git`, and network access to kernel.org, snapshot.ubuntu.com
and github.com. No root access, system packages or global configuration are
needed; everything is staged inside the clone. The project normally runs under
nono for confinement (see README), but reproduction does not depend on it.

## 1. Stage the pinned dependencies

```sh
python3 scripts/stage-resources.py packages          # 222 Ubuntu packages -> .tools/sysroot (GCC, QEMU, Python, ...)
python3 scripts/stage-resources.py sources --sources linux   # Linux 6.12.110 -> .deps/linux
python3 scripts/restore-toolchains.py --only lean    # Lean 4.33.1 -> .tools/lean
```

- Packages come from the Ubuntu snapshot of 2026-09-20 and are checked against
  `dependencies/packages.lock.json`.
- The Linux archive is checked against `dependencies/sources.lock.json`.
- Lean comes from its official release, which is identical to the locked
  snapshot file by file. Its hash is in `dependencies/toolchains.lock.json`.

Syzkaller, Firecracker, Go, the Lean MCP server and the reference
documentation are not needed for the check. The first two can be staged with
`--sources`, but GitHub archive downloads are not guaranteed byte-stable.

## 2. Build and verify the oracle kernel

```sh
LEANUX_KERNEL_PROFILE=net-choice LEANUX_KERNEL_BUILD=.artifacts/kernel-net-choice scripts/in-bundle scripts/build-kernel
scripts/in-bundle python3 scripts/kernel-identity.py .artifacts/kernel-net-choice
```

The profile extracts the locked Linux archive into
`.artifacts/src/linux-6.12.110-choice-stream-d1` and applies one patch there,
strictly and by hash (`scripts/apply-kernel-patch.py`):
`kernel/patches/choice-stream.patch` (generated from the locked source by
`kernel/patches/gen-choice-stream.py`). It records every random draw and
clock read at generic interception points into the KCOV stream
(`kcov_choice_ip`), lets a trace steer named call sites, and collects the
trace's deferred units in dispatch sections: `process_one_work` and the
NET_RX vector open a KCOV remote section for each dispatch of a function in
the dispatch set the guest arms (`harness/linux.py`, `DISPATCH_SYMBOLS`).
It touches no WireGuard file; `kernel/patches/wireguard-kcov-remote.patch`
(per-site sections) is used only by the older profiles.

Every line number in the files the check anchors is preserved. `.deps` is
never modified. The identity must equal the first hash in
`kernel/identity-x86_64-net-choice.txt`.
The `vmlinux` file hash itself differs between build directories, because the
debug info and build IDs record the path; the identity excludes exactly that.
If the identity differs, stop: the check's decision table was verified against
the accepted build.

## 3. Run the check

```sh
scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_wg harness.test_noise harness.test_linux
scripts/in-bundle python3 -m evaluator.check --suite wireguard        # ~3 minutes
scripts/in-bundle python3 -B -m unittest evaluator.test_model_replay  # recorded replays; needs the check's build
scripts/in-bundle python3 -m evaluator.check                          # everything, ~1.5 hours
```

The full check writes `.artifacts/check/<timestamp>/report.json` and exits
nonzero unless every trace agrees. Compare it with the recorded result
([stage A report](docs/2026-09-30-wireguard-stage-a-report.md), section 2):

| Field | Expected |
|---|---|
| `status` | `pass` |
| `traces` / `operations` | 1288 / 38652 |
| `counts` | `{"agreement": 1288}` |
| `operand_pairs_matched` | 324964 |

The generated traces are seeded (`--seed 20260920`, the default), so the trace
set is the same. The guest runs QEMU TCG with one CPU, so the coverage is
deterministic; `chunk_splits` may vary with console output size and does not
affect results. `chunk_retries` lists the chunks run a second time after a
guest timeout or a busy QEMU slot (at most once each; never after a
mismatch); on a contended host it may be non-empty.

## What is not reproduced

- `.artifacts/runs/evidence` (the recorded reports) is not in Git. The
  expected numbers above come from it.
- Mutants: `scripts/in-bundle python3 scripts/wg-mutants.py` (about 20
  minutes) applies each stage A mutant to a clean tree and requires it to be
  rejected.
