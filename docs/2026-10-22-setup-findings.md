# Setup findings and follow-up

These findings were discovered during the front-facing documentation review,
starting at main `c63423ef`. Each entry distinguishes an open repair from a
fix carried into this documentation branch from main.

[USER 2026-10-22] Track setup defects found during the documentation review for
separate repair by the coordinating agent. Keep reproduction commands and the diagnosis here;
transient test output is not retained.

## F1: D1 key test failed after the state split

**Resolved on main at `c65cf6ae` (repair `ec5d25e8`).**
`harness.test_d1_keys.D1KeysTest.setUpClass` generated a
Lean driver using the old state representation. Its unqualified `M` was
ambiguous between `WG.M` and `Leanux.M`, and it constructed a `World` with
obsolete `k`, `env`, `timing` and `hidden` fields while omitting the new
`ambient`, `tasks` and `fs` fields. The driver failed to elaborate, so the
suite did not run its key vectors. That was a test failure, not a successful
cryptographic validation. The repair qualifies `WG.M`, constructs the current
subsystem worlds and serializes the fixed-width birthdates; it preserves the
vectors and their assertions.

From a prepared task worktree, check the repaired suite with:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/in-bundle lake build leanux-model leanux-fixed-width-tests
cap scripts/in-bundle python3 -B -m unittest harness.test_d1_keys
```

The failure was first observed in the old setup guide's expanded command:
173 tests ran, with one setup error and one skipped test. The required
five-module fast tier was then checked independently: 144 tests, zero failures
and one skip because its default kernel path had no build. Model/default
library builds passed without warnings.

The [repaired suite](../harness/test_d1_keys.py) now belongs to the required
six-module fast tier in `AGENTS.md` and the first-run guide. The integration
record reports its five isolated tests passing. The counts above describe
the original failure and its investigation, not the current fast tier.

## F2: worktree guide gives an obsolete guest-slot default

**Fixed on `task/shop-window`; source checked.**
[docs/worktree-practices.md](worktree-practices.md) now states that
`LEANUX_QEMU_SLOTS` defaults to 16, matching
[harness/linux.py](../harness/linux.py), `AGENTS.md` and the shop-window guides.
The former value of 8 was a documentation error; runtime concurrency is unchanged.

## F3: the former Lean setup could not supply the pinned toolchain

**Resolved by launcher change `2933b4e9`, landed on main at `fe9c755b`.**
The old first-run guide used `scripts/restore-toolchains.py --only lean`.
The [toolchain lock](../dependencies/toolchains.lock.json) has two Lean rows:
4.33.1 has an upstream source, but the required 4.35.0 has only a local
snapshot that is not in Git. From a fresh clone, the old command downloaded
4.33.1 and then failed with `No snapshot and no upstream release for lean`.
The former launcher also required a staged toolchain, so installing Lean
through elan alone did not make that setup work.

The [first-run guide](../REPRODUCING.md#1-prepare-the-environment) now installs
the exact `lean-toolchain` pin through elan. The launcher accepts that
installed toolchain after trying a matching staged snapshot, checks its
version and refuses an unversioned Lean from `PATH`. It does not install or
download a toolchain itself. The lock is unchanged: snapshot restoration
remains the devboxes' [offline mechanism](offline-usage.md#restore-the-devboxes-lean-snapshots),
with its two-row and archive requirements stated there.

## F4: working-practices example names an absent oracle directory

**Open documentation proposal; source and artifact checked.**
[AGENTS.md](../AGENTS.md#build-test-and-check) gives
`.artifacts/kernel-net-choice-e2` in the original clone as an example oracle
path. That directory is absent on the shared development machine. The approved
build is in `.artifacts/kernel-net-choice-s5`; its `vmlinux` SHA-256 is
`06513d05fc37506b6cea546e8f11b9fe328e482265341ca41c242157bfa5e88e`, matching
the [pinned identity](../kernel/identity-x86_64-net-choice.txt).

Proposed correction for the maintainer to approve: replace the obsolete
example with the `-s5` directory, while retaining the requirement to set an
absolute `LEANUX_KERNEL_DIR` and verify the identity. The directory name is
not an identity check or a promise that a clone contains the build. This
documentation pass does not edit `AGENTS.md`.
