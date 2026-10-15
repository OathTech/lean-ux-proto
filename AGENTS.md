# Repository working rules

This file holds the standing rules and the commands. Decisions, with their
dates and provenance, are in [docs/decisions.md](docs/decisions.md); plans and
designs are in `docs/`. Edit this file in place when a practice changes, and
put a changed rule to the user before changing it here.

## Behavioral mirror at the thin-layer altitude; theorems only in the proof tree

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

The mirror covers single-CPU WireGuard, stopping at WireGuard's boundary (the
IP stack only where WireGuard's paths or observables depend on it), with
pipes, eventfd and epoll over the file-descriptor slice, and seccomp (the
filter chain, the classic-BPF checker and translation, the sandboxed child).
A gap is excluded only for a profound reason, recorded in the
design doc. The next targets and the proof campaign are recorded in
[docs/decisions.md](docs/decisions.md) and
[the campaign charter](docs/2026-10-13-charter-proof-campaign.md); the dated
documents are indexed in [docs/README.md](docs/README.md).

Theorems live only in the proof tree, `Leanux/Proofs/`, its own lake target
`LeanuxProofs` outside the default build; its map and its register of
results are [docs/proofs.md](docs/proofs.md). Proofs are a validation
channel for the models beside the differential check, under Rule Zero:
(1) the mirror might be wrong; (2) the kernel might contain bugs; (3) the
former is much more likely than the latter [USER 2026-10-14]. A discrepancy
is read in that order and a statement is never bent to accommodate one. The mirror
(`Leanux/FS`, `Leanux/WG`, `Leanux/Kernel`, `Leanux/Env`,
`Leanux/Runner.lean`) carries no theorem, no proof-shaped restructuring, and
no change made to let a proof close: a proof that cannot close is a report
against the mirror, settled by the differential check, never by editing the
mirror to fit the statement. Proofs about the mirror and about models
layered on it are in scope; a simulation proof against the C is not, until
the user opens it. No proof-audit infrastructure beyond the axiom check
below, and no theorem is an acceptance gate for mirror work.

The register names, per result, the mirror commit it holds over and whether
it is current or lagging. A mirror change may land while a result lags; its
integration record says so, and the repair is a follow-on task on the proof
tree, not a condition on the mirror change. Every claim point reports the
lag.

Keep later proof work cheap: follow the conventions marked "Adopt as a
convention" in sections 3(a), 3(b), 3(d), 3(e) and B7 of
[the future-proof-paths note](docs/2026-10-06-future-proof-paths.md) and
the ones in [the window-proof conventions](docs/2026-10-13-window-proof-conventions.md).

## Build, test and check

On the shared devboxes, run every build, check, mutant set and kernel build
through the box's `capped` wrapper (`~/.claude/CLAUDE.md`); a KILLED banner
(exit 137) is a failure. The checker and `scripts/build-kernel` use the wrapper
themselves when it is installed and run uncapped with a notice when it is not:
it is a box matter, not a project requirement.

```sh
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
capped -- scripts/in-bundle python3 -m evaluator.check --suite wireguard   # about 3 minutes
capped -- scripts/in-bundle python3 -m evaluator.check                     # everything: about an hour
LEANUX_KERNEL_PROFILE=net-choice capped -m 64G -- scripts/in-bundle scripts/build-kernel
```

Point `LEANUX_KERNEL_DIR` at the approved oracle build (an absolute path, for
example `.artifacts/kernel-net-choice-e2` in the main checkout). The check and
every guest boot compare the build's identity with
`kernel/identity-x86_64-net-choice.txt` and refuse any other build; a control
kernel is named with `LEANUX_KERNEL_IDENTITY`.

Full checks, mutant sets and kernel builds are long. Start them as tracked
background tasks that report completion. Never detach one with `&` and poll by
process name: the poller matches itself and never exits. Before reporting
progress, check actual completion.

Validation is scoped to the change:
- at a claim point: the full check, the controls and the sentinel mutants
  once; during a task, the suites the change touches;
- every agent gets an explicit scope, a time or run budget, and a stop
  condition ("report rather than fix if ...");
- no unrequested harness, guest or kernel changes during a validation task:
  report the finding instead.

The host has 32 cores and is usually under-used: use it. `LEANUX_QEMU_SLOTS`
is 16 (the default; guests are single-threaded at 256 MiB), builds and suite
runs run concurrently with other agents' runs, and every heavy job stays
inside `capped`. Budget timeouts with headroom. A failure that depends on scheduling order is a modeling gap: fix it
in the environment model (`Leanux/Env.lean`) with an exact, fail-closed rule,
never with a retry. A rerun happens at most once, only on an infrastructure
outcome, and is recorded in the report
([the contended-host note](docs/2026-10-06-contended-host.md)).

## Gates and speedbumps

The claim is data and control-flow equivalence of the executable mirror with
Linux. It rests on three gates, and only these block:
- the model build and the unit tests, the fast tier that guards every commit;
- the differential check on the approved oracle at a claim point (an
  integration, a stage), with its fail-closed guards on the instruments
  (records dropped, unconsumed or at the wrong site, an unlisted function
  covered, a schedule not consumed exactly);
- the kernel identity check, which refuses to boot any other build.

The proof tree makes a separate claim and has its own gate, run at its
claim points (a merge of the tree) and not on mirror commits:
`capped -- scripts/in-bundle scripts/proof-gate`, which builds `LeanuxProofs`
(about three minutes), prints the axioms of every declaration of every
`Statements.lean` under `Leanux/Proofs/` and fails on any beyond `propext`,
`Classical.choice` and `Quot.sound`, fails on `sorry`, `admit`, `axiom`,
`native_decide`, `unsafe`, `implemented_by` or `extern` anywhere in the
tree, and fails if anything outside the tree imports it, if the root
`Leanux/Proofs.lean` misses a result's `Statements`, or if `LeanuxProofs` is
a default lake target.

The user-opened binary adequacy charter has a separate standalone target:
`capped -- scripts/proof-gate --binary` builds `binary/`, prints its headline,
frame, witness and composition axioms, and checks its proof sources for
escapes. Its claim-point kernel replay/toolchain commands are in
[binary/README.md](binary/README.md); this does not add a mirror acceptance
gate.

Everything else is a speedbump: cheap, run at claim points, never blocking
intermediate work, built to catch honest drift and not adversarial attack:
- the negative control suites (`corpus/*-controls`, their scripts);
- the sentinel mutants (`scripts/wg-mutants.py`, `scripts/pipes-mutants.py`):
  one per verdict channel and record instrument, each on the smallest corpus
  subset that rejects it, about half an hour in all.

A new check rule is added when it is cheap and catches a real class of
mistake. A new instrument on the trust surface (a record kind, a comparison
class, a section rule) gets a one-off mutant, run once and reported in its
commit, then deleted unless it replaces a sentinel. No evidence bundles,
integration records or run narratives: a merge commit's message carries the
run's counts and the user's signoff.

The mirror (`Leanux/FS`, `Leanux/WG`, `Leanux/Kernel`) contains only the C's
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
  final step before updating `main`. The merge commit's message carries the
  run's counts and the user's words. Additional unapproved changes require
  new signoff.
- While awaiting signoff, preserve the branch, keep `main` unchanged, and
  follow the registered worktree cleanup policy.

This rule takes precedence over older project documents that permit autonomous
integration or minimize human checkpoints. Autonomous work may continue within
authorized scope on non-main branches; the user-signoff requirement for `main`
remains mandatory.

## Recording decisions

A decision is logged where it is made, with its provenance (user or agent):
in the commit message, in the design doc it belongs to, and in
[docs/decisions.md](docs/decisions.md) when it is a standing one. This file
carries no decision history and no session state.

## Kernel findings

A kernel behaviour that might concern its maintainers, found by the
differential check, a correspondence audit or the proof campaign, is written
up in [docs/upstream-tray/](docs/upstream-tray/INDEX.md) as a numbered
report: the C lines in the pristine source, the classification (true bug,
design nuance, observability gap or question) with its argument, the
reproducer in this repository's corpus and what a reader without it would
do, the impact, and how it was found. The tray holds reports only: no patch
branches, no upstream pull requests from this repository; filing is the
user's call. A finding never changes the mirror, which follows the code as
it is, and the trace that shows it stays in the corpus so the behaviour
remains checked.
