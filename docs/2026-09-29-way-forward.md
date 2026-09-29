# Way forward — assessment and proposal, 2026-09-29

Status: **PROPOSAL, not adopted.** Drafted by an agent [AGENT] at the user's
request. It changes no policy until the user approves it. Each decision below
is marked [USER] (stated by the user, with date) or [AGENT] (proposed by the
agent, awaiting approval).

## 1. Direction (as stated by the user)

- [USER 2026-09-29] The mirror is a purely operational, executable behavioral
  model of what the Linux code does. This project proves **no theorems**: not
  about the mirror, not between Lean encodings, and not the Linux↔mirror
  simulation. Proving invariants of the mirror, or proving that Linux refines
  it, are possible later tasks, done elsewhere.
- [USER 2026-09-29] The mirror is the thin layer in the middle. It is low enough
  that a later simulation proof is easy, and high enough to avoid reasoning
  about real C semantics. The principle is to **abstract away C semantic detail
  but keep a simple correspondence of data and control flow**:
  - kernel data structures map to mirror state of the same shape;
  - the C's choice points correspond to choice points in the mirror.

  A separation-logic triple can then host the relation R(linux_state,
  mirror_state).
- [USER 2026-09-29] The anticipated proof tool is a Cerberus-based separation
  logic. The early prototype is `../cerberus-sl`. It is deliberately simple; a
  RefinedC-like workhorse logic is planned but not yet available. Its present
  limits are not constraints on the mirror.
- [USER 2026-09-29] The harness is overbuilt for the assurance it needs and
  should be cut back (section 5).

## 2. Assessment of the current state

Three read-only reviews were run on 2026-09-28/29:

- model fidelity against `.deps/linux`;
- evidence and infrastructure;
- process and alignment.

A fourth read-only survey covered `../cerberus-sl`.

### 2.1 What is solid

- **The model is behaviorally correct on its tested domain.** Every guard, its
  order, and its errno in `Leanux/FS` and `Leanux/Runner.lean` matches the
  pinned C, for all seven operations. Examples:
  - the write-overflow `>` guard (`fs/eventfd.c:262`);
  - `dup3` onto a live fd;
  - `next_fd` updates (`fs/file.c:529,566`);
  - `F_GETFL` = 2050 (`fs/anon_inodes.c:122`).
- **The recorded evidence is genuine.** It covers:
  - 35 handwritten traces with 245 operations, run 3 times;
  - 1,000 generated traces with 34,932 operations;
  - 32 critic traces with 480 operations.

  All of them agree. There are no mismatches, timeouts, or unknowns. The model
  identity in the evidence matches the Lean sources on `main`.
- **The Linux runner is good engineering and is kept.** It consists of
  `harness/guest.c`, `harness/linux.py`, the trace contract, and per-operation
  KCOV. It runs a fresh QEMU guest per run and a fresh child per trace.

### 2.2 What is not

1. **The model is collapsed below the target altitude**, specifically in the
   fd-table and VFS layers:
   - **Bitmaps.** There are no `open_fds`/`close_on_exec` bitmaps. `alloc_fd`
     sets these bits at reservation (`fs/file.c:531-535`); the model's `allocFd`
     only moves `nextFd`, and `fdInstall` does the rest. The intermediate state
     the C passes through therefore does not exist in the mirror.
   - **Merged objects, no refcounts.** `struct file` and `eventfd_ctx` are
     merged into one object. There are no refcounts, and objects are never
     released. `doDup2` is one install step; the C's `get_file`, the `-EBUSY`
     branch, and `filp_close(tofree)` (`fs/file.c:1228-1241`) are missing.
   - **No VFS dispatch.** There is no `vfs_read`/`vfs_write` step, so the
     `f_mode` checks and the `f_op` dispatch (`fs/read_write.c:553-555`) are
     absent.
   - **User copy is fused.** `copy_to_iter` is fused with the counter update. As
     a result, "EFAULT after decrement" (`fs/eventfd.c:235,243`) cannot be
     expressed.
   - **Fixture policy leaks into kernel code.** The rules "fds 0–7 are never
     valid", "limit = 32", and "status flags = 2050" appear in kernel-model
     code. A single `limit` conflates RLIMIT with `max_fds`.
   - **The eventfd counter layer is already at the right altitude.**
     `eventfdCtxDoRead` has two steps, matching `fs/eventfd.c:180-181`.
2. **Step correspondence is asserted, not checked.**
   - Branch "labels" are strings. The evaluator checks only that they come from
     an allowed set, and Linux reports `branches: []`.
   - KCOV PCs are symbolized to source lines but never compared with anything.
   - The ~2,000 lines of correspondence JSON are careful bookkeeping of branch
     dispositions. They contain no intermediate-state or update-order evidence.
3. **Testing is weaker than the counts suggest.**
   - Only syscall `(ret, errno, bytes)` is compared.
   - Generated traces never hit EMFILE.
   - About 56% of generated operations are EBADF paths.
   - No test has ever exposed a real model bug.
   - The "independent" critic traces are 4 templates with 8 parameter choices
     each, written by the same worker.
   - No syzkaller-derived trace has ever run against Linux.
4. **No committed code reproduces the evidence.** The runs predate the evaluator
   commit (`adfb767`), and the driver that produced them is not in the repo.
   There is no single command that builds the model, runs Linux, and compares.
5. **Process dominates substance.** About 440 lines of model and runner sit
   against ~7,000 lines of infrastructure and process, plus ~3,300 lines of plan
   documents. The remaining campaign gates (G2 agent-repair exercise, G3
   evaluator mutants and sandbox probes, G4 resume exercise) mostly test the
   agent workflow, not the mirror.
6. **The repository contradicts itself.**
   - `main` still carries proofs and proof gates.
   - The proof removal (`task/remove-model-proofs`, 46fb38f) is unmerged.
   - Status lines in `README.md`, `project-objectives.md`, and
     `prototype-plan.md` still say that the model does not exist.
   - The untracked ledger (`.artifacts/runs/campaign.json`) runs ahead of
     `main`.

### 2.3 Are we moving towards the goal?

**Partly.** The foundations that matter, a correct small mirror and a reliable
Linux runner, exist. Most effort since 2026-09-20 went into trust boundaries,
ledgers, and proof machinery that is now out of scope. The central open
question, the altitude of the mirror, was never addressed directly.

The good news is that the model is ~150 lines. Restructuring it to the target
altitude is cheap now and gets more expensive with every operation added.

## 3. Design principles for the mirror layer [AGENT, derived from section 1]

These turn the user's principle into checkable rules. The fit with a
RefinedC/Iris-style logic is noted where the cerberus-sl survey informed it.

1. **One mirror structure per C struct on the path.** Use C field names and
   widths:
   - `Task {files, rlimitNofile}`
   - `FilesStruct {nextFd, fdt}`
   - `Fdtable {maxFds, fd, openFds, closeOnExec}`
   - `File {fFlags, fMode, fCount, kind, privateData}`
   - `EventfdCtx {kref, count, flags}`

   Abstraction rules:
   - Pointers become abstract identities.
   - Each object is owned once, in an identity-keyed store.
   - Descriptor slots hold identities, not ownership.

   This is the shape a big separating conjunction over owned objects relates
   naturally. Aliasing then needs no fractional permissions.
2. **Abstract values only where R can say exactly how.**
   - Keep refcounts (`fCount`, `kref`) as explicit fields, even when they are
     unobserved at the syscall boundary. Every `get_file`/`fput` becomes a
     mirror step.
   - Bitmaps may become pure sets. Derived optimisations (`full_fds_bits`) may
     be dropped, with a note of the C invariant that makes this sound.
3. **One mirror function per C function, or per lock-delimited region.** Use the
   same arguments and the same call structure. Each function has shape
   `(state, args) → (result, state')`, which is exactly the form a
   `ProcContract` with the mirror state as its logical variable can state.

   Include small helpers where they carry state changes: `alloc_fd`,
   `find_next_fd`, `fd_install`, `__put_unused_fd`, `file_close_fd_locked`,
   `filp_close`/`fput`, `do_dup2`, `ksys_dup3`, `do_eventfd`,
   `vfs_read`/`vfs_write` dispatch, `eventfd_read`, `eventfd_ctx_do_read`,
   `eventfd_write`, and `do_fcntl`.
4. **Keep the C's choice points in the C's order.**
   - Every C branch on the path is present in the mirror.
   - If a branch is out of scope, it is an explicit, fail-noisy `unsupported`
     result, never an omission.
   - Choice points decided by the environment (allocation failure, table
     expansion, RLIMIT, user-copy fault) take an explicit oracle argument
     rather than being excluded by the trace domain.
5. **Explicit cut points for mechanisms not modeled.** These become named
   contracts with an obligation recorded next to the step:
   - spinlocks and `file_lock` (lock-held regions are atomic mirror steps);
   - RCU publication;
   - wait queues and wakeups (a recorded no-op when there are no waiters);
   - `copy_*_user`;
   - `expand_fdtable`;
   - `array_index_nospec`;
   - `current`/`rlimit`.
6. **Typed step trace instead of string labels.** There is one constructor per C
   decision point, each carrying its source anchor (`file:line`). The
   correspondence then lives in the code; there is no separate JSON registry.
7. **Fixture policy lives only in the runner.** Fixture fds 0–7 become ordinary
   occupied, foreign files in the initial state. Constants such as 8, 32, and
   2050 are computed or passed in, never hard-coded in the FS layer.
8. **C-shaped encodings where cheap.** Examples: negative errno returns,
   explicit `(unsigned int)` casts, and `f_flags` computed by the C's two mask
   steps.

The cerberus-sl survey records two cross-project gaps. Neither blocks this
work, and both are flagged for the logic's roadmap:

- the workhorse logic has no design yet for refcounts or counting ghost state;
- nested structs, stored function pointers (`f_op`), and casts are deferred past
  R3.

## 4. What assurance we actually need [AGENT]

The mirror's claims are behavioral and structural. The checks should be exactly
these:

| # | Check | Mechanism |
|---|---|---|
| A1 | Observable agreement | Corpus plus seeded generated traces, run on Linux and the mirror, compared literally. Timeouts, crashes, and unknowns fail. |
| A2 | Control-flow agreement | Per operation, the mirror's typed step trace is compared with the source lines that Linux's KCOV PCs map to, restricted to modeled functions. A spike must first establish how precise this can be under inlining (section 6, phase 3). |
| A3 | Structural review | Each mirror function is reviewed against its C function, and the review is recorded in the code's doc comment with the source anchor. A changed function needs a fresh review. The reviewer is an agent or the user; the diff to `main` is approved by the user. |
| A4 | Reproducibility | One command reproduces A1 and A2 from committed sources and the pinned kernel. |

Explicitly **not** needed at this stage:

- a contributor/evaluator trust boundary against malicious agents;
- sandbox escape probes (the user excluded security tasks on 2026-09-21);
- submission allowlists;
- freeze contracts;
- job resume;
- an injected-fault agent-repair demonstration;
- gate ledgers.

The user's signoff on `main` is the trust boundary.

## 5. Harness remediation plan [AGENT]

Aim: under ~1,500 lines of infrastructure around the model, with one entry
point.

| Keep (maybe simplify) | Replace | Remove from the tree (git history keeps them) |
|---|---|---|
| `harness/guest.c`, `harness/linux.py`, `harness/trace.py` | `evaluator/{runner,experiment,protocol,process}.py` → a single `check` module/CLI: build, run Linux, run model, compare, KCOV cross-check, one report | `evaluator/{boundary,submission,proofs}.py`, `evaluator/ProofAudit.lean` |
| `contracts/trace-v1.md`, `trace.schema.json`, `observation.schema.json` | `correspondence/*.json` (~2,000 lines) → source anchors and review notes in the Lean doc comments, plus A2 | `contracts/{freeze-v1,submission-v1,proof-v1,proof-identities-v1}` |
| `evaluator/generate.py` (generator and minimizer), `evaluator/coverage.py` | `docs/*` (11 files) → `README.md`, this plan once adopted, `offline-usage.md`; move the rest to `docs/history/` | `Leanux/Proofs`, `Leanux/Reference` (via the 46fb38f branch) |
| `corpus/` | `scripts/worktrees` + `check-worktrees.py` (618 lines, ledger-coupled) → plain `git worktree add .worktrees/<id> -b task/<id>` documented in a few lines (user decision D3) | `scripts/check-evaluator-boundary.py`, `check-isolation.py`, `nono-check-profile.json`, `dependencies/sandbox-validation.json` |
| `kernel/config-x86_64`, `scripts/build-kernel`, `scripts/in-bundle`, the dependency locks | `.artifacts/runs/campaign.json` gate ledger → retired; the evidence directory stays as untracked history | — |
| `scripts/capture-correspondence.py`, reduced to emitting preprocessed translation units for the modeled files (a useful future input for the logic) | — | — |
| Provisioning scripts (`stage-resources`, `probe-toolchains`, toolchain cache/restore, lean manual mirror): kept, but off the main path | — | — |

`harness/syzkaller_adapter.py` stays parked: kept, and not part of the check
until there is a reason.

Order matters. Build `check` first and confirm that it reproduces the existing
agreement on the current model. That becomes the regression oracle for
everything else. Delete afterwards.

## 6. Phased plan [AGENT]

Each phase ends with a branch, its diff, and the check output. These are
presented for user signoff before anything reaches `main`.

- **Phase 0: consistent state.**
  - Amend `task/remove-model-proofs` so its `AGENTS.md` wording states the
    principle in section 1 (data and control-flow correspondence at the
    thin-layer altitude). Its current "each computational step must correspond"
    reads as C-level.
  - Remove the sandbox, confinement, and agent-repair gates from the
    plan/objectives it carries, or supersede those documents with this plan.
  - Merge on signoff.
  - Delete the fully integrated `task/linux-runner` and
    `task/source-correspondence` refs (with user approval).
- **Phase 1: single check command.**
  - Implement `check` (A1 + A4).
  - Reproduce the recorded agreement on the current model from committed code.
    This closes the evidence-provenance gap.
  - Then remove the retired modules (section 5).
- **Phase 2: restructure the model to the principles in section 3.**
  Observable behavior must stay identical: `check` stays green on the whole
  corpus. Work in this order:
  1. C-shaped structures and the fixture moved to the runner;
  2. `alloc_fd`/`fd_install`/bitmaps;
  3. refcounts, file and ctx separation, `do_dup2`/close release paths;
  4. VFS dispatch;
  5. user-copy steps and the environment oracle;
  6. the typed step trace.
- **Phase 3: control-flow agreement (A2).**
  - Spike: for 3–4 operations, compare the mirror's step anchors with the
    KCOV→line map and measure false positives and negatives under inlining.
  - Then add the check.
- **Phase 4: widen the domain.**
  - Add the currently unreachable but modeled cases: EMFILE in generated
    traces, blocking-mode creation with would-block outcomes, `dup3`/`close`
    onto a fixture fd, and nonzero getter arguments.
  - Rebalance the generator away from EBADF.
  - Retain naturally found disagreements as regressions.
- **Later, by user choice:** the next component (e.g., pipes or epoll), and
  handing the eventfd read path to the workhorse logic as a first target.

## 7. Decisions needed from the user

| ID | Decision |
|---|---|
| D1 | Approve this proposal (or amend it) as the governing plan, superseding `project-objectives.md` and `prototype-plan.md`. |
| D2 | Merge `task/remove-model-proofs` after the Phase 0 amendments. This needs explicit signoff on the concrete diff. |
| D3 | Replace the ledger-coupled worktree manager with plain `git worktree` use. The `AGENTS.md` worktree and main-signoff rule is unchanged. |
| D4 | Removed files: delete from the tree (history keeps them), or move to `docs/history/`/`attic/`. |
| D5 | Delete the refs `task/linux-runner` and `task/source-correspondence`. |
| D6 | What were the "classifier interruptions" recorded as unresolved in the ledger? Retire the note if they no longer matter. |
| D7 | Reviewer mix: Fable for model-vs-C structural reviews (A3), Opus for implementation and cleanup? |
