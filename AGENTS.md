# Repository working rules

## Behavioral mirror at the thin-layer altitude; no theorem proving

The user set this direction on 2026-09-22 and restated it on 2026-09-29. The
current plan is [the way-forward plan](docs/2026-09-29-way-forward.md).

The deliverable is a purely operational, executable Lean mirror of the
configured Linux code, tested against actual kernel behavior. It is a thin
middle layer:
- low enough in operational detail that a later separation-logic simulation
  proof against the C is straightforward;
- high enough to avoid modeling C semantics (memory model, GNU C, byte-level
  representation).

The governing principle is to **abstract away C semantic detail, but keep a
simple correspondence of data and control flow**:
- kernel data structures map to mirror state of the same shape;
- each C choice point on a modeled path has a corresponding mirror choice point,
  in the same order;
- out-of-scope branches are explicit, fail-noisy outcomes, never omissions.

Matching only syscall results is insufficient. The design rules are in section 3
of the plan.

Do not build theorems of any kind:
- no proofs about the mirror;
- no proofs between Lean encodings;
- no simulation proofs;
- no proof-audit infrastructure.

Do not add them as acceptance gates. Historical proof artifacts and older plans
in `docs/history/` do not authorize recreating them.

## Worktrees and user signoff for main

This is a core trustworthiness requirement, explicitly set by the user on
2026-09-22. It applies to every agent, including the coordinator.

- All development takes place in task or integration worktrees on branches
  other than `main`. This includes code, documentation, configuration, builds,
  and tests. Never edit tracked files or make development commits in the
  main checkout.
- Use the main checkout for read-only inspection, shared inputs, worktree
  administration, and integration explicitly approved by the user. Follow
  `docs/worktree-practices.md` for shared dependencies, private outputs, and
  cleanup.
- **Merging to `main` always requires explicit user signoff for the concrete
  changes being integrated.** This applies to local and remote `main`, and to
  every equivalent way of advancing it: fast-forward, cherry-pick, rebase,
  reset, direct commit, push, or automated merge.
- Permission to implement a task, run a long-cycle goal, operate autonomously,
  or integrate worker changes on a non-main branch is not permission to update
  `main`. Passing checks, agent reviews, and earlier merge approvals do not
  authorize a new merge.
- Prepare the complete change and relevant validation in worktrees first.
  Present its branch/commit and reviewable diff, then obtain user signoff as the
  final step before updating `main`. Record that approval with the integration
  record. Additional unapproved changes require new signoff.
- While awaiting signoff, preserve the branch and evidence, keep `main`
  unchanged, and follow the registered worktree cleanup policy.

This rule takes precedence over older project documents that permit autonomous
integration or minimize human checkpoints. Autonomous work may continue within
authorized scope on non-main branches; the user-signoff requirement for `main`
remains mandatory. The rule is prospective; no remediation of earlier commits
was requested.
