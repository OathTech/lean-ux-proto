# Repository working rules

## Worktrees and user signoff for main

This is a core trustworthiness requirement, explicitly set by the user on
2026-09-22. It applies to every agent, including the coordinator.

- All development takes place in task or integration worktrees on branches
  other than `main`. This includes code, documentation, configuration, builds,
  tests, and proofs. Never edit tracked files or make development commits in the
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
