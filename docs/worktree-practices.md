# Worktrees, shared dependencies, and cleanup

Status: operating policy for the [prototype plan](prototype-plan.md), recorded
2026-09-20. The worktree manager and shared-input/private-output launcher support
are implemented and passed the [bootstrap acceptance exercise](../reports/worktree-bootstrap.md).
The original size and untracked-file inventory below records the pre-campaign
state; the intended project files have since been committed without bulk data.

## Separate source, shared inputs, and disposable outputs

Use Git worktrees for task source changes. Git shares its object database across
worktrees; each checkout gets its own tracked files and index. The ignored
dependency directories do not get copied by `git worktree add`.

The inspected workspace contains approximately 4.8 GiB in `.deps`, 4.2 GiB in
`.tools`, 1.6 GiB in `.cache`, and 2.2 GiB in `.artifacts`. The Git database is
about 224 KiB. Most current setup and planning files are still untracked; only
the original brainstorming note is in HEAD. A new worktree at that HEAD would
therefore omit the setup scripts and current plans.

Keep the main checkout as the coordinator's integration workspace and the home
of shared staged inputs. Put managed checkouts under `.worktrees/<task-id>/`
inside this project, never in a neighboring project. Use one task branch per
worker, starting from a recorded accepted commit.

| State | Ownership and treatment |
| --- | --- |
| Project source, schemas, small corpora, proofs, reports | Tracked files checked out separately in each worktree |
| `.tools` and pinned archives/reference documentation | One shared copy; candidate access is read-only |
| Linux source and accepted oracle kernel/tool outputs | Coordinator-owned, versioned shared inputs; read-only during evaluation |
| `.deps/go-mod` | Preserve the complete offline module store; use read-only where supported and serialize any required maintenance |
| Syzkaller source/generated files/binaries | Shared accepted version; its existing build mutates the source tree, so rebuilding is a coordinator-owned, serialized operation |
| Lean `.lake`, temporary files, writable caches, guest outputs | Private to the task or evaluation attempt; removable after evidence promotion |
| Accepted evidence and minimal failure bundles | Stored outside disposable worktrees, with retained source identities |

Never copy the complete main checkout to provision a task. Do not hard-link
writable build trees: writes would affect the same underlying files. Ordinary
worktrees need no full dependency copy, and reflinks are unnecessary for the
default workflow. A special experiment that needs modified kernel or dependency
source gets an explicitly budgeted, versioned input rather than modifying the
shared accepted copy while workers use it.

## Bootstrap before agent fan-out

1. Establish a small initial commit containing the intended project files and
   ignore rules. Review the explicit file list; never commit `.deps`, `.tools`,
   caches, worktrees, or build outputs. Use repository-local Git settings only.
   Record the baseline commit before task creation.
2. Verify that ordinary Git worktree metadata operations work inside the active
   nono session. Do not bypass a denied Git boundary or change a shared profile.
   If unavailable, report the concrete constraint and use the plan's small source
   snapshot fallback for independent work until worktrees can be used.
3. Teach the launchers to distinguish the task source root, shared input root,
   and attempt output/cache root. The present `scripts/in-bundle` assumes they
   are colocated; merely adding a worktree is not sufficient.
4. Give each attempt its own cache, temp, Lean build, guest output, and result
   locations. Existing smoke scripts use fixed output paths and must be adapted
   before concurrent use. Preserve the current single-checkout defaults.
5. Validate create, run, resume, and remove on two disposable worktrees before
   delegating implementation tasks.

Prefer explicit shared-input paths in trusted launch configuration. If a tool
requires a conventional path, a task-local symlink may expose a shared directory;
it does not grant write access or make that directory disposable. Child nono
profiles must grant access to the resolved shared inputs and restrict writes to
the private attempt directories. Never share the main `.cache` as a writable
task cache. Its existing wrapper links contain absolute paths and need deliberate
handling when separating roots.

Publish accepted tools and oracle outputs before admitting dependent work. Reuse
the pinned oracle kernel for ordinary model repairs. Kernel changes use a unique
out-of-tree output directory and a separate identity; do not rebuild one kernel
per Lean worktree. Share additional build results only if their source, tool,
configuration, and build-option identities match and candidates cannot modify
the published artifacts. Candidate-generated build caches are not trusted inputs
for independent acceptance.

## Ownership and concurrency

The coordinator alone creates, integrates, renames, removes, or prunes managed
worktrees and updates the shared dependency inputs. Workers edit their assigned
checkout and produce patches or local task commits. Integration runs through the
existing independent evaluator; a worker cannot declare its own result accepted.

Allow at most three worker worktrees plus one temporary evaluation worktree.
Paused or quarantined trees count toward that limit. Evaluation can reuse a clean
registered evaluation checkout sequentially, provided each acceptance attempt
gets fresh private outputs. Observe the plan's aggregate CPU, memory, and guest
limits across all checkouts.

Register task ID, canonical path, branch/base/head identities, owner and active
jobs, private output/cache paths, disk usage, and cleanup state in the durable
ledger outside the worktree. Worktrees share Git metadata; serialize integration
and administrative operations. They isolate source edits, not hostile agents
with broad project access, and do not replace the evaluator's OS boundary.

## Automatic teardown

Run this lifecycle after task integration or abandonment, at coordinator restart,
and before admitting new work when the disk budget is tight:

1. Stop the task's workers and jobs through the recorded process supervision.
   Confirm no live owner or process still uses its checkout or outputs. A stale
   PID or an old modification time alone is not sufficient evidence.
2. Preserve work: record commits or patches, include needed untracked source
   files, and promote compact reports, proofs, corpora, and minimal failure
   bundles to durable locations. Check the promoted artifacts and references
   before deleting their originals. Keep a Git ref for any unmerged commit still
   needed by evidence; a hash written in a report does not keep an object alive.
3. Inventory tracked changes, untracked files, and ignored contents. Delete only
   registered disposable outputs belonging to the finished attempt. Do not follow
   symlinks into shared inputs or traverse an arbitrary path supplied by a worker.
   Unknown files or unexpected changes cause quarantine for coordinator review,
   not automatic data loss or an immediate human approval request.
4. Remove the checkout using `git worktree remove` after it is clean. Do not use
   blanket `git clean -fdx`, forced worktree removal, or recursive deletion over
   the project/worktree parent. An unexpected refusal becomes a cleanup task.
5. Delete a task branch only after integration and evidence retention are
   verified. An unmerged branch can be retained without retaining a heavyweight
   checkout. Do not delete unrelated refs or manually remove `.git/worktrees`.
6. Inspect stale metadata with `git worktree prune --dry-run`. Pruning removes
   stale administrative records, not live working directories. Prune only when
   the reviewed entries are known managed, finished tasks; do not disturb other
   worktrees or locked entries. Record reclaimed space and final lifecycle state.

The cleanup helper must validate paths against the coordinator's registry,
canonical managed roots, and expected task identity. Use a lifecycle lock so
creation, admission, and removal cannot race. It must never remove the main
checkout, shared stores, or an active task, including when an agent supplies an
unexpected path or symlink.

Successful scratch outputs are removed promptly after acceptance and evidence
promotion. Failed attempts retain small reproducible bundles; large intermediate
builds are retained only while useful to an active diagnosis. Do not keep a
separate full build directory for every repair attempt indefinitely. Long-lived
evidence has its own inventory and retention references so cleanup remains
possible without destroying reproducibility.

## Disk accounting and acceptance

The existing plan's 8 GiB additional-artifact budget covers worktrees, private
caches, all task/evaluation outputs, and new shared artifacts together. It is
not an allowance per worker. Retain the 5 GiB free-space floor and record actual
usage before and after tasks. Count shared stores once; do not dereference their
symlinks when estimating per-worktree usage. Stop new admissions before exceeding
the budget, reclaim registered disposable state, and retain unresolved evidence.

Do not delete the current kernel builds or other existing artifacts merely
because several appear similar. Readiness reports reference particular files
and hashes. Reconcile those references before any later, separately scoped
compaction. Dependency archives and `.deps/go-mod` are never cleanup candidates.

The bootstrap acceptance exercise must demonstrate all of the following:

- Two worktrees see the intended baseline source and the same shared input
  identities without copying the large stores.
- Lean and C probes use isolated writable outputs and run successfully in both;
  shared inputs remain unchanged. Test write denial with disposable decoys under
  equivalent grants, following the evaluator's boundary-probe policy.
- Changed source in one task does not alter the other's source or acceptance
  outputs; no generated kernel image or module cache appears per task by default.
- A simulated interruption resumes the registry correctly. Active, dirty,
  unregistered, and symlink-escape cases are protected from accidental deletion.
- Promoted evidence remains replayable after both disposable worktrees and their
  registered scratch state are removed through the normal lifecycle.
- Disk usage returns to the measured baseline plus the intentionally retained
  small evidence. Neither Git's worktree list nor the registry retains an
  unexplained orphan.

This is an automatic bootstrap gate before sustained parallel work. It adds no
human checkpoint and does not require a cleanup daemon or machine-wide service.
