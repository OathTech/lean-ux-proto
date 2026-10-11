# Repository working rules

This file holds the standing rules and the commands. Decisions, with their
dates and provenance, are in [docs/decisions.md](docs/decisions.md); plans and
designs are in `docs/`. Edit this file in place when a practice changes, and
put a changed rule to the user before changing it here.

## Behavioral mirror at the thin-layer altitude; no theorem proving

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
- out-of-scope branches are explicit, fail-noisy outcomes, never omissions;
- hidden inputs (randomness, clocks, allocation outcomes, dispatch order) are
  recorded at their kernel source and consumed by the mirror in order, so the
  mirror is a deterministic function of the trace and those records.

Matching only syscall results is insufficient. The design rules are in section
3 of [the way-forward plan](docs/2026-09-29-way-forward.md) and in
[the choice-stream strategy](docs/2026-10-03-choice-stream-strategy.md).

The current target is complete coverage of single-CPU WireGuard, stopping at
WireGuard's boundary (the IP stack only where WireGuard's paths or observables
depend on it), with pipes as the scale test. A gap is excluded only for a
profound reason, recorded in the design doc. The stage order and the work on
branches are in [the pause-state note](docs/2026-10-08-pause-state.md).

Do not build theorems of any kind:
- no proofs about the mirror;
- no proofs between Lean encodings;
- no simulation proofs;
- no proof-audit infrastructure.

Do not add them as acceptance gates. Historical proof artifacts and older plans
in `docs/history/` do not authorize recreating them.

Keep later proof work possible without doing it: follow the conventions
marked "Adopt as a convention" in sections 3(a), 3(b), 3(d), 3(e) and B7 of
[the future-proof-paths note](docs/2026-10-06-future-proof-paths.md).

## Build, test and check

Run every build, check, mutant set and kernel build through the box-wide
`capped` wrapper (`~/.claude/CLAUDE.md`). A KILLED banner (exit 137) is a
failure. The checker wraps its own model build, and `scripts/build-kernel`
wraps the kernel `make`; `LEANUX_CAPPED` overrides the wrapper's path.

```sh
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_wg harness.test_linux
capped -- scripts/in-bundle python3 -m evaluator.check --suite wireguard   # about 3 minutes
capped -- scripts/in-bundle python3 -m evaluator.check                     # everything: about an hour
LEANUX_KERNEL_PROFILE=net-choice capped -m 64G -- scripts/in-bundle scripts/build-kernel
```

Full checks, mutant sets and kernel builds are long. Start them as tracked
background tasks that report completion. Never detach one with `&` and poll by
process name: the poller matches itself and never exits. Before reporting
progress, check actual completion.

Validation is scoped to the change:
- mutants (`scripts/wg-mutants.py`, `scripts/pipes-mutants.py`) run for the
  mirror files a change touches, on a reduced corpus; the full set runs once,
  at a milestone;
- every agent gets an explicit scope, a time or run budget, and a stop
  condition ("report rather than fix if ...");
- no unrequested harness, guest or kernel changes during a validation task:
  report the finding instead.

The host is shared. Keep `LEANUX_QEMU_SLOTS` at 3 and budget timeouts with
headroom. A failure that depends on scheduling order is a modeling gap: fix it
in the environment model (`Leanux/Env.lean`) with an exact, fail-closed rule,
never with a retry. A rerun happens at most once, only on an infrastructure
outcome, and is recorded in the report
([the contended-host note](docs/2026-10-06-contended-host.md)).

## Checks must pay for themselves

- The goal is data and control-flow equivalence of the executable mirror with
  Linux. The checker (`evaluator/`, `harness/`, `correspondence/`) serves that
  goal.
- A new check rule or instrument must state what it catches that the existing
  ones do not, with evidence: a real defect or a mutant it alone rejects. One
  that cannot show this is not added, and one that stops paying is removed.
  Finer-grained instruments are fine; checkers that merely accrete are not.
- The one exception: a cheap check that closes a fail-open (silent-pass) hole
  may be kept without a mutant, after the conflict and the cost are put to the
  user and the user says yes for that check.
- The mirror (`Leanux/FS`, `Leanux/WG`, `Leanux/Kernel`) contains only the C's
  data and control flow. Fixture, scheduling and timing assumptions live in
  the environment model (`Leanux/Env.lean`) or the runner.

## Oracle kernel changes

Classify every change to the oracle kernel before building it.
- Record-only or steer-only changes (new choice records, capture hooks,
  steering lookups, dispatch-cap sizes) are approved as a class. Each still
  lands with the normal per-merge signoff, with the new kernel identity and
  patch hash recorded.
- Changes that alter kernel behaviour or configuration (config options, boot
  parameters, functional patches) each need their own case put to the user.
- If the class is unclear, treat the change as a behaviour change.

## Worktrees and user signoff for main

This is a core trustworthiness requirement. It applies to every agent,
including the coordinator.

- All development takes place in task or integration worktrees on branches
  other than `main`. This includes code, documentation, configuration, builds,
  and tests. Never edit tracked files or make development commits in the
  main checkout.
- Use the main checkout for read-only inspection, shared inputs, worktree
  administration, and integration explicitly approved by the user. Follow
  [docs/worktree-practices.md](docs/worktree-practices.md) for shared
  dependencies, private outputs, and cleanup. Remove a worktree, naming its
  path, once its branch has landed or is abandoned.
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
  record (`.artifacts/runs/evidence/<id>/integration.json`). Additional
  unapproved changes require new signoff.
- While awaiting signoff, preserve the branch and evidence, keep `main`
  unchanged, and follow the registered worktree cleanup policy.

This rule takes precedence over older project documents that permit autonomous
integration or minimize human checkpoints. Autonomous work may continue within
authorized scope on non-main branches; the user-signoff requirement for `main`
remains mandatory.

## Recording decisions

A decision is logged where it is made, with its provenance (user or agent):
in the commit message, in the design doc it belongs to, and in
[docs/decisions.md](docs/decisions.md) when it is a standing one. This file
carries no decision history and no session state.
