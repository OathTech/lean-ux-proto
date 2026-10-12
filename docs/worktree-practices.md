# Worktrees and shared dependencies

Status: current practice under the [way-forward plan](2026-09-29-way-forward.md),
adopted 2026-09-29 (decision D3). It replaces the ledger-coupled worktree
manager ([history](history/worktree-practices-2026-09-20.md)). The
[AGENTS.md](../AGENTS.md) rule is unchanged: all development happens in
worktrees on non-`main` branches, and `main` moves only with explicit user
signoff on the concrete diff.

## Create

```sh
git worktree add .worktrees/<id> -b task/<id> main
cd .worktrees/<id>
scripts/in-bundle python3 -m evaluator.check     # or any other bundled command
```

`scripts/in-bundle` detects a Git worktree automatically:

- **Shared inputs.** `.tools`, `.deps` and the pinned kernel builds come from
  the main checkout and are read-only.
- **Private state.** `.cache`, `.artifacts` and `.lake` are created inside the
  worktree. They are Git-ignored and disappear with it.
- **Guests.** Only one QEMU guest runs at a time, across all checkouts, through
  `.artifacts/runs/qemu.lock` in the main checkout.

Never copy the main checkout to create a task. Never write into `.tools`,
`.deps` or the accepted kernel build. A kernel or dependency change needs its
own versioned output directory, agreed with the user.

## Remove

After the branch is merged, or explicitly abandoned:

```sh
git -C .worktrees/<id> status --porcelain     # must be empty; commit or discard first
git worktree remove .worktrees/<id>           # ignored build outputs do not block removal
git branch -d task/<id>                       # -d refuses unmerged work; keep the ref if still needed
```

Do not use `git clean -fdx`, and do not delete recursively over `.worktrees/`.
Keep a ref for any unmerged commit a design doc or a commit message refers to.
