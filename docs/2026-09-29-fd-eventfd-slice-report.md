# FD/eventfd slice: final report, 2026-09-29

Status: closing report for the first slice, as section 2.4 of the
[next plan](2026-09-29-next-plan.md) requires. It is written by the agent
[AGENT], and its evidence is listed in section 5.

## 1. What the mirror covers

- **Kernel:** Linux 6.12.110 at `fa5b068`, x86-64, the repository's
  configuration (`CONFIG_SECURITY=n`, `CONFIG_MODULES=n`, no networking).
- **System calls:**
  - `eventfd2`, `dup`, `dup3`, `close`, `read`, `write`;
  - `fcntl`: `F_GETFD`, `F_SETFD`, `F_GETFL`, `F_SETFL`.
- **Domain:**
  - one sequential task with a private `files_struct`;
  - `RLIMIT_NOFILE` from 8 to 1024, so the table grows past its embedded 64
    slots;
  - nonblocking or blocking eventfds, as long as no operation would wait;
  - valid user buffers;
  - allocation and user-copy outcomes supplied by an explicit environment
    oracle, which always succeeds in the harness.

**Mirror modules.** They follow the C files: 1,063 lines of operational Lean,
excluding the decision table and runner.

| Lean module | C source mirrored |
|---|---|
| `FS/File.lean` | `fs/file.c`: the table, bitmaps, `alloc_fd` with its retry, `expand_files`/`expand_fdtable`/`alloc_fdtable`/`copy_fdtable`, `fd_install`, close, dup/dup3, `__fget_*`, `fdget*` |
| `FS/FileTable.lean` | `fs/file_table.c`: file allocation and initialisation, `fput`/`__fput`/`__fput_sync`, `file_free` |
| `FS/EventfdOps.lean`, `FS/Eventfd.lean` | `fs/eventfd.c`; `__refcount_sub_and_test` through `kref_put` |
| `FS/Open.lean`, `FS/Close.lean` | `fs/open.c`: `filp_flush`, `filp_close`, close |
| `FS/ReadWrite.lean` | `fs/read_write.c`: `ksys_read`/`write`, `vfs_read`/`write`, `rw_verify_area`, `new_sync_read` |
| `FS/Fcntl.lean` | `fs/fcntl.c`: fcntl, `do_fcntl`, `setfl` |
| `FS/AnonInodes.lean` | `fs/anon_inodes.c` |

**Correspondence.**
- **State:** one structure per C struct (`Fdtable`, `FilesStruct`, `Task`,
  `File`, `EventfdCtx`), finite and comparable.
- **Decisions:** 185 C decision points, recorded in C order. 74 are declared
  value comparisons, and 8 are declared repeatable (`alloc_fd`'s `repeat:`
  loop).
- **Cut points:** locks, RCU, wait queues, pure helpers
  (`find_next_zero_bit`, `roundup_pow_of_two`, `bitmap_copy_and_extend`),
  accounting, `ida_alloc`, `call_rcu`, `inode_owner_or_capable`.
- **Checked assumptions.** Several facts the mirror assumes are confirmed by
  Linux's comparison records rather than taken on trust:
  - the harness is owner-or-capable (it runs as root);
  - the anonymous inode's `i_flags` and file type.

## 2. What is checked, and how strongly

One command (`python3 -m evaluator.check`, about 5 minutes) runs 1,073 traces:
41 handwritten, 32 critic, and 1,000 generated v2 traces drawn from mirror-filtered
candidates. Each runs on the pinned kernel in QEMU, twice (PC and comparison
KCOV modes), and on the mirror.

| Check | Result on the final run |
|---|---|
| Behavior: return, errno, bytes | all agree |
| Control flow: two-sided KCOV witnesses, unreported decisions | all agree; 131 of 185 decisions have witnesses, and the rest have reasons verified against the binary |
| Order within each C function | all agree |
| Declared comparisons: operands against `KCOV_TRACE_CMP` | 311,894 pairs match |
| Determinism: the comparison rerun gives identical results and bytes | holds |

**Planted bugs rejected.** Five mutants, four of them behavior-preserving:
- a changed guard;
- a collapsed branch;
- a dropped last-reference release;
- reordered checks;
- a wrong `max_fds` of 128 instead of 64.

**Coverage of C arms.** 49 decisions see both outcomes, and 12 are never
evaluated. Every remaining arm needs fault injection, concurrency, other file
types, or a wait, each of which is out of this slice's domain.

## 3. Residual gaps (accepted for the prototype)

Listed in detail in [correspondence/README.md](../correspondence/README.md):
- An outcome with no KCOV witness can be wrongly reported or omitted without
  detection. These are mostly one-line error arms.
- Order is not compared across C functions.
- The operand order of non-constant comparisons cannot be checked.
- A C site evaluated several times in one operation, while the mirror reports
  it once, is not detected (repeatable decisions aside).
- The system-wide `nr_files` is approximate by design (percpu), so it is not
  modeled.
- Fixture files (console, KCOV, `/dev/null`) are opaque: any operation on
  their `f_op` or inode is `unsupported`.

## 4. Effort and lessons, for the next component

- **Size.** About 1,060 lines of mirror plus a 714-line decision table cover
  the modeled paths of seven C files. The size of those C paths was not
  measured; by inspection it is on the order of 1,500 lines. The decision table is
  mostly mechanical once the C is read. Its spans, reasons and comparison
  specs are validated against the binary, so errors are caught quickly.
- **What mattered most:**
  - Deriving KCOV witnesses from source spans and instrumented lines, instead
    of hand-picking them.
  - Requiring an explicit, verified reason for every unwitnessed outcome.
  - Checking operands. It caught a divergence (`max_fds`) that neither
    behavior nor control flow shows.
- **Recurring compiler effects.** Each is documented where it occurs:
  - shared epilogue blocks;
  - hoisted loads;
  - constant folding;
  - branch-free selects;
  - tail calls into the coverage hook;
  - comparison attribution to a neighboring line in multi-line conditions.
- **Structural review.** An independent Fable review of the finish-up found no
  correspondence errors. Its tightenings are applied: one more declared
  comparison, a narrower repeatable set, and three assumptions turned into
  checked facts.
- **Process lessons:**
  - Mutant runs must work from a committed tree, and each mutant must be
    verified as applied before it runs.
  - Independent reviews found real fail-open paths in every phase.
- **Tooling reusable for the next component:**
  - the check command and the KCOV/comparison tooling;
  - the decision-table conventions;
  - mirror-filtered generation.

  The QEMU guest, the fixture and the trace language are specific to this
  slice and will need extending (for WireGuard: netlink, sockets, packets).

## 5. Evidence

| What | Where |
|---|---|
| Final check and mutant reports | `.artifacts/runs/evidence/phase4-domain/` (recorded when this branch is finalized) |
| Earlier phases | `.artifacts/runs/evidence/{phase1-check,phase2-mirror,phase2b-repr,phase3-order}/`, each with its `integration.json` signoff record |
