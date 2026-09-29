# Lean-ux prototype

This repository develops an executable Lean mirror of Linux, beginning with a
small file-descriptor/eventfd slice. The mirror is a purely operational,
behavioral model. It abstracts away C semantic detail but keeps a simple
correspondence of data structures and control-flow choice points with the
configured Linux code, so that a later separation-logic simulation proof can
relate the two. That proof, and any theorems about the mirror, are outside this
project. Executable behavior is tested against the pinned kernel. See
[the repository rules](AGENTS.md).

- [Current plan: assessment and way forward (2026-09-29)](docs/2026-09-29-way-forward.md)
- [Worktree, shared dependency, and cleanup practices](docs/worktree-practices.md)
- [Offline development setup and environment audit](docs/offline-development.md)
- [Using the staged offline environment](docs/offline-usage.md)
- [Pinned source identities](dependencies/sources.lock.json)
- [Superseded plans and handoffs](docs/history/README.md)

Status (2026-09-29): the FD/eventfd mirror and the QEMU Linux runner exist and
agree on the recorded corpora. The plan above covers the next steps:
- a single check command;
- a cut-back harness;
- restructuring the mirror to C-shaped data and control flow;
- KCOV-based control-flow checks.

The earlier campaign ledger and its gates are retired.

## Checking the mirror

```sh
scripts/in-bundle python3 -m evaluator.check                   # everything: ~3 minutes
scripts/in-bundle python3 -m evaluator.check --trace alias_close  # replay one case
scripts/in-bundle python3 -m evaluator.check --suite handwritten --no-build
```

The check builds `leanux-model`, runs the handwritten, critic and seeded generated
traces on the pinned Linux guest (QEMU, fresh child per trace, per-operation KCOV)
and on the mirror. It then requires two things:
- literal agreement of every observation;
- consistency of every model branch label with the Linux coverage
  ([anchors](correspondence/README.md)).

It writes `report.json` under `$LEANUX_ARTIFACTS/check/` and exits nonzero
unless everything passes. Unit tests:
`scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_syzkaller_adapter`.
Work happens in worktrees; see [worktree practices](docs/worktree-practices.md).

## Environment

Use the pinned tools inside your normal nono session:

```sh
scripts/in-bundle python3 scripts/probe-toolchains.py
scripts/in-bundle python3 scripts/check-guest.py
```

`scripts/in-bundle` selects local tools, headers, libraries, firmware and caches.
It creates no sandbox or namespaces; nono provides confinement. Your existing
`~/.config/nono/profiles/codex-local.json` can be used without modification.
Run `scripts/check-nono` for an acceptance suite under a separate nono test
profile that blocks networking. See [nono setup](docs/nono-profile-proposal.md).

Bulk dependencies and build outputs are Git-ignored; preserve them when copying
this workspace for offline use. The bootstrap runtime is Linux x86-64 with
glibc 2.39 or newer, `/bin/sh`, Python 3, and nono.
