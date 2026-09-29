# Worktree bootstrap acceptance

The first campaign bootstrap passed on 2026-09-20. Source baseline:
`7c791782e3552e24a13633b2cffab2b9614b928b`. The original planning/setup baseline is
`dbe225c`; no bulk staged dependencies were committed.

The executable check is:

```sh
python3 scripts/check-worktrees.py
```

Each invocation uses unique task IDs and records evidence under
`.artifacts/runs/evidence/<bootstrap-id>/`. The first run's full report is
[the local bootstrap report](../.artifacts/runs/evidence/bootstrap/report.json).
Its 26 checks cover:

- Lean/Std native builds and GCC/Clang C and GCC C++ builds in two worktrees.
- Shared tool identities, separate caches/artifacts, and nested launcher switching.
- Read-only shared-input decoys and denial of IPv4/IPv6 TCP/UDP socket creation.
- Source isolation, dirty/active/unregistered/unknown-output/symlink cleanup refusal.
- A surviving child process preventing ownership release after its leader exits.
- The aggregate artifact admission budget.
- Interrupted creation and interrupted teardown, recovered through the registry.
- Removal of both checkouts and scratch directories, followed by replay from
  promoted Lean/C sources and inspection for orphaned Git metadata.

The shared dependency store was not copied. Both task branches and worktrees
were removed after verified evidence promotion. Existing kernel images, staged
sources, and module caches were retained.

`scripts/worktrees` provides create, list, acquire, release, remove, and reconcile
operations. Cleanup requires a hashed receipt under `.artifacts/runs/evidence`.
The coordinator owns lifecycle operations. `scripts/in-bundle` reads managed
workspace settings and exports separate `LEANUX_ROOT`, `LEANUX_SHARED_ROOT`,
`LEANUX_CACHE_ROOT`, and `LEANUX_ARTIFACTS` paths. These settings select paths;
actual write restrictions come from nono.

This establishes the worktree bootstrap only. G1–G4 remain pending. Candidate
evaluation still needs the full protocol, proof, process-interference, inherited
descriptor, and timeout-boundary checks specified by the master plan. Shared
collaboration-agent access remains the documented trust limitation.
