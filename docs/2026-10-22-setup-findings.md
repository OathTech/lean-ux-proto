# Setup findings for overseer follow-up

These setup findings were discovered while reviewing the
front-facing documentation against main `c63423ef`. Documentation corrections
are on `task/shop-window`; the harness and build scripts are unchanged.

[USER 2026-10-22] Track setup defects found during the documentation review for
repair by the overseer. Keep reproduction commands and the diagnosis here;
transient test output is not retained.

## F1: optional D1 key test fails after the state split

**Open; reproduced.** `harness.test_d1_keys.D1KeysTest.setUpClass` generates a
Lean driver using the old state representation. Its unqualified `M` is
ambiguous between `WG.M` and `Leanux.M`, and it constructs a `World` with
obsolete `k`, `env`, `timing` and `hidden` fields while omitting the new
`ambient`, `tasks` and `fs` fields. The driver fails to elaborate, so this
suite does not run its key vectors. This is a test failure, not a successful
cryptographic validation.

From a prepared task worktree, reproduce with:

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

Repair the generated Lean driver in [harness/test_d1_keys.py](../harness/test_d1_keys.py)
to use the current subsystem worlds and monads while preserving the vectors'
assertions. Re-run the isolated suite and the expanded setup command. Do not
skip the suite or weaken its expected key values to make it pass.

The first-run guide now uses the required five-module tier and explicitly
names this outstanding failure. Remove that caveat once the repair passes.

## F2: worktree guide gives an obsolete guest-slot default

**Fixed on `task/shop-window`; source checked.**
[docs/worktree-practices.md](worktree-practices.md) now states that
`LEANUX_QEMU_SLOTS` defaults to 16, matching
[harness/linux.py](../harness/linux.py), `AGENTS.md` and the shop-window guides.
The former value of 8 was a documentation error; runtime concurrency is unchanged.
