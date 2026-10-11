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
- [Next plan: finish the slice, then WireGuard (2026-09-29)](docs/2026-09-29-next-plan.md)
- [WireGuard stage A report (2026-09-30)](docs/2026-09-30-wireguard-stage-a-report.md)
- [WireGuard stage B1 report (2026-09-30)](docs/2026-09-30-wireguard-stage-b1-report.md)
- [WireGuard stage B2 report (2026-10-01)](docs/2026-10-01-wireguard-stage-b2-report.md)
- [WireGuard stage C report (2026-10-01)](docs/2026-10-01-wireguard-stage-c-report.md)
- [Reproducing the results from a clone](REPRODUCING.md)
- [Worktree, shared dependency, and cleanup practices](docs/worktree-practices.md)
- [Using the staged offline environment](docs/offline-usage.md)
- [Pinned source identities](dependencies/sources.lock.json)
- [Superseded plans and handoffs](docs/history/README.md)

Status (2026-09-30): the FD/eventfd slice and WireGuard stages A and B1 are
mirrored with C-shaped data and control flow. Stage A covers netlink
configuration, the allowed-IPs trie, peers and keys; stage B1 covers
transmission and routing. They agree with the networking oracle kernel on
behavior, KCOV control flow and comparison operands for 1,310 traces. Stage
B2 adds the receive path up to Noise, observed through remote KCOV on a
patched kernel. After a drift audit (2026-09-30), checks must pay for
themselves; see AGENTS.md.

## Checking the mirror

```sh
scripts/in-bundle python3 -m evaluator.check                   # everything: ~1.5 hours
scripts/in-bundle python3 -m evaluator.check --suite wireguard # ~3 minutes
scripts/in-bundle python3 -m evaluator.check --trace alias_close  # replay one case
scripts/in-bundle python3 -m evaluator.check --suite handwritten --no-build
```

On the shared devboxes, run each of these through the box-wide memory-cap
wrapper: `capped -- scripts/in-bundle ...`. The check wraps its own model build
with it, and `scripts/build-kernel` wraps the kernel `make`; `LEANUX_CAPPED`
overrides the wrapper's path (default `/usr/local/bin/capped`).

The check builds `leanux-model` and runs the handwritten, critic, WireGuard and
seeded generated traces on the networking oracle kernel (`LEANUX_KERNEL_DIR`,
built as in [REPRODUCING.md](REPRODUCING.md); its identity must be the one in
`kernel/identity-x86_64-net-choice.txt`, or the check refuses to boot it) and
on the mirror:
- the guest is QEMU, with a fresh child per trace in each of two KCOV modes;
- generated traces are kept only where the mirror places them inside the
  domain.

It then requires:
- literal agreement of every observation;
- agreement of every mirror decision with Linux's coverage, including order
  within each C function;
- agreement of every declared comparison's operands with Linux's comparison
  records.

See [correspondence](correspondence/README.md).

It writes `report.json` under `$LEANUX_ARTIFACTS/check/` and exits nonzero
unless everything passes. Unit tests:
`scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_wg harness.test_linux`.
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
this workspace for offline use, or stage them from the locks as in
[REPRODUCING.md](REPRODUCING.md). The bootstrap runtime is Linux x86-64 with
glibc 2.39 or newer, `/bin/sh`, Python 3, and nono.

## License

GPL-2.0-only; see [LICENSE](LICENSE). The mirror follows the structure of
Linux, which is GPL-2.0-only, so the repository uses the same license (not
"or later", which would be incompatible with GPL-2.0-only code). Staged
third-party sources and packages (`.deps`, `.tools`, not in Git) keep their
own licenses.
