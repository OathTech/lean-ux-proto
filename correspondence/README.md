# Configured source and correspondence

These files relate the mirror to the native x86-64 Linux 6.12.110 build at commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c`. The governing principle is in
[AGENTS.md](../AGENTS.md): abstract away C semantic detail, but keep data and
control-flow choice points aligned with the C. The design rules are in section 3
of the [way-forward plan](../docs/2026-09-29-way-forward.md).

## Where the correspondence lives

The correspondence lives in the Lean sources, not in a separate registry.

- **State.** `Leanux/Kernel/Defs.lean` has one structure per C struct:
  - `Fdtable`, `FilesStruct`, `Task`, `File` and `EventfdCtx`;
  - fields named as in the C;
  - pointers replaced by identities into owned stores;
  - `f_count` and `kref` kept explicitly.
- **Functions.** `Leanux/FS/*.lean` has one Lean function per C function on the
  path, in modules named after the C files (for example `File.lean` for
  `fs/file.c`). Each doc comment gives the C lines it mirrors. Lock
  acquire/release, RCU and cut-point contracts are noted at the C's position.
- **Decisions.** `Leanux/Kernel/Decision.lean` has one constructor per C
  decision point. Each has its label, its condition site, and the source spans
  that run only for each outcome. The mirror records `⟨decision, outcome⟩`
  where the C evaluates the condition, in the C's order.
- **Unsupported paths.** Paths the mirror does not model end in a fail-noisy
  `unsupported` outcome, never a silent default. Examples: blocking waits,
  table expansion, and waiters on the wait queue.
- **Environment.** Outcomes decided by the environment consult an explicit
  oracle (`EnvSite`); the harness oracle says every site succeeds. Examples:
  allocation, `ida_alloc`, `access_ok`, and user copies.

## Control-flow check (A2)

`python3 -m evaluator.check` reads the decision table from `leanux-model
--decisions`. It computes from the built kernel image which source lines own a
KCOV instrumentation point, and in which (inlined) functions
(`evaluator/coverage.py`). The scan:
- includes split bodies (`.cold`, `.part`);
- includes call sites of callees that tail-jump, directly or conditionally,
  into `__sanitizer_cov_trace_pc`;
- fails if a listed function or a called symbol is missing, or if a function
  owns no point.

`kcov.json` lists the anchored files and the functions to scan.

An outcome's **witnesses** are the instrumented lines of its span. Blank lines,
braces, labels and comments are dropped from spans; statements are kept.

**Loading the table** fails unless:
- labels are unique;
- spans are in anchored files, inside the file, within a window around the
  condition line, and do not overlap between outcomes;
- the condition line is a statement;
- every decision's C function (the label prefix) owns instrumentation.

**The reason rule.** A side with no witnesses must declare why (below), and a
declared reason on a witnessed side fails. So a reason can neither be missing
nor hide evidence.

**Per operation**, each of the following fails the check:
- a decision reported more than once;
- a reported outcome that covers none of its witnesses;
- a reported outcome whose opposite outcome's witnesses are covered;
- a decision the mirror did not report, but whose witnesses Linux covered;
- a covered line inside a span that the instrumentation map does not know;
- an unknown label, or an operation with no decision;
- coverage only outside the anchored files.

**Reasons** (`Unobservable` in `Leanux/Kernel/Decision.lean`):

| Reason | Meaning |
|---|---|
| `shared_continuation` | The outcome continues into code the other outcome also runs. |
| `shared_operand` | A short-circuit operand sharing its line or body. |
| `branch_free` | The value is selected without a branch. |
| `no_instrumentation` | The span owns no point; verified. |
| `compiler_shared` | A shared block is attributed to the span's line; commented at the decision. |
| `outside_domain` | A `BUG_ON` trap. |
| `constant_folded` | The configured build folds the test away. |
| `same_line` | A `WARN_ONCE` body on the condition's line. |
| `inline_helper` | Evaluated in a helper outside the span window. |

**Residual gaps**, which coverage alone cannot close:
- An unobservable outcome could be reported where the C never evaluates it,
  or omitted where it does. This affects arms like one-line `return -EINVAL;`
  error exits, which in this build own no instrumentation point. A
  "decision was reached" rule was evaluated and rejected: under DWARF
  attribution, condition-line coverage fails for 11 decisions whose condition
  lines are instrumented.
- Witnesses are keyed by source line, not by inline context. A header helper
  inlined into an unmodeled caller in the same operation could in principle
  satisfy a witness.
- Step order within an operation is not yet checked (Phase 3).

These are mitigated by structural review of each function against the C.

The report's `decision_coverage` lists, per decision, how often each outcome
occurred. It also lists which outcomes KCOV can witness, which decisions the
corpus never evaluates, and which it sees with one outcome only.

## Configured source capture

`scripts/in-bundle python3 scripts/capture-correspondence.py`:
- reads the accepted kernel build's `.cmd` records;
- preprocesses the modeled translation units serially with the exact GCC
  command;
- writes `.i` files, line maps, the include closure with hashes, and a
  comparison of every source input against the pinned archive.

`--verify PATH` rechecks a captured manifest. `capture-v1.json` records the
retained capture. It is source provenance and a fixed C text for later proof
work, not evidence of agreement.

## Domain facts

The trace domain has these properties. `contracts/scope-v1.json` records the
same facts in machine-readable form.
- Fixture descriptors 0–7 are reserved. They are modeled as fixture files whose
  operations are outside the slice.
- `RLIMIT_NOFILE` is 32, while the initial table capacity is 64.
- Eventfds are nonblocking.
- The file status is computed as in the C: `O_RDWR | O_NONBLOCK` = 2050.
- Close-on-exec is descriptor-local.
- Descriptor references keep their number after close.
