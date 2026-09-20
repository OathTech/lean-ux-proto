# Lean-ux prototype

This repository develops an executable Lean mirror of Linux, beginning with a
small file-descriptor/eventfd slice. Behavioral experiments and computational
correspondence prepare the model for local simulation proofs. The prototype also
establishes an independently checked workflow for sustained agent construction
and repair.

- [Project objectives](docs/project-objectives.md)
- [Prototype master plan: goal entry point and acceptance gates](docs/prototype-plan.md)
- [Worktree, shared dependency, and cleanup practices](docs/worktree-practices.md)
- [Original research note](docs/2026-09-19-rough-plan.md)
- [Earlier plan review and semantic slice details](docs/2026-09-20-prototype-proposal.md)
- [Offline development setup and environment audit](docs/offline-development.md)
- [Pinned source identities](dependencies/sources.lock.json)
- [Using the staged offline environment](docs/offline-usage.md)

The offline dependency bundle is staged locally and verified with a kernel boot,
KCOV collection, Lean/C builds, syzkaller builds, and Lean language-server
diagnostics. The semantic model, differential harness, contributor evaluation
boundary, and proofs remain future work. The execution plan uses four work
phases, automatic gates, parallel workers, one informational midpoint check-in,
and a final review.

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
