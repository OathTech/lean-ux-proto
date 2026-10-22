# How the model is checked against Linux

Lean-ux aims to preserve the data structures and control-flow choices of the
configured Linux code, while abstracting away C memory representation. The
checker tests this correspondence on operation traces; it does not prove it.
The [project health warning](../README.md) applies. Normal oracle checks use
the kernel build pinned by
[`identity-x86_64-net-choice.txt`](../kernel/identity-x86_64-net-choice.txt).

## Where to look

| Part | Location |
| --- | --- |
| Kernel-shaped state, with identities in place of pointers | [`Leanux/Kernel/Defs.lean`](../Leanux/Kernel/Defs.lean), [`Leanux/WG/Types.lean`](../Leanux/WG/Types.lean), [`Leanux/WG/State.lean`](../Leanux/WG/State.lean) |
| Functions following the C, with source sites and abstraction boundaries in comments | [`Leanux/FS/`](../Leanux/FS/), [`Leanux/WG/`](../Leanux/WG/), [`Leanux/Net/`](../Leanux/Net/), [`Leanux/Seccomp/`](../Leanux/Seccomp/) |
| Branch labels, condition sites and outcome source spans | [`Leanux/Kernel/Decision.lean`](../Leanux/Kernel/Decision.lean) |
| Fixture, timing, stack and scheduling assumptions | [`Leanux/Env.lean`](../Leanux/Env.lean), [`Leanux/Env/`](../Leanux/Env/) |
| Anchored C files, functions and declared coverage exceptions | [`kcov.json`](kcov.json) |
| Coverage mapping and comparison | [`evaluator/coverage.py`](../evaluator/coverage.py), [`evaluator/check.py`](../evaluator/check.py) |

The built model exports its decision table with `leanux-model --decisions`
and its hidden-input sites with `leanux-model --hidden-sites`. Unsupported
paths stop with a source site; invariant failures and inconsistent input
records are errors, never successful observations.

## What a passing check means

For the selected traces, the checker requires:

1. **Observable agreement:** syscall results, error numbers, read data and
   operation-specific outputs such as WireGuard packets and counters agree.
2. **Branch agreement:** model decisions agree with Linux's KCOV coverage at
   their declared source spans. Observable decisions are checked for order
   within each C function.
3. **Operand agreement:** declared value comparisons match Linux's comparison
   records, accounting for compiler transformations such as operand reordering.
4. **Consistent recorded inputs:** modeled random draws, clocks, allocation
   outcomes and deferred dispatches consume their records at the expected
   sites and in the required order.

The guest runs separately for PC and comparison coverage; its observable
results must agree between those runs. Unknown sites, missing records,
unconsumed modeled inputs and execution failures fail the check. Explicitly
declared records below an abstraction boundary are handled separately and
reported in `choice_records_skipped`.

## Recorded inputs and reconstructed schedules

Recording dispatch order does not capture every scheduling choice. Two
reconstructions matter when interpreting agreement:

- **NAPI poll placement.** Some records leave open whether a receive poll
  happened before or after a peer reference was released. The checker tries
  the allowed placements, uses comparison operands to select them, and
  replays the selected combination. It requires matching results and control
  flow and the rule's independence conditions; otherwise it fails. The report
  names selected before-release sections in `napi_before_put_sections`.
- **Encrypt-worker yield position.** A reschedule record says a worker
  yielded, but not how many items it processed first. `Leanux/Env/Batch.lean`
  reconstructs this from the recorded transmit work under a restricted rule.
  A schedule outside the rule is refused.

These are explicit inferences from execution evidence, not independently
recorded inputs. In particular, comparison operands used to select a schedule
are also part of the agreement check. See
[`evaluator/check.py`](../evaluator/check.py) (`section_agreement` and `replay_problem`),
[`Leanux/Env/Batch.lean`](../Leanux/Env/Batch.lean), and the
[dispatch-order design](../docs/2026-10-11-dispatch-order.md).

## Limits of the evidence

The model covers selected paths of a single-CPU kernel. Environment assumptions
and operations below the modeled boundary are explicit contracts, not checked
C implementations. Generated candidates outside the modeled domain are
filtered before guest execution and reported in `domain_filtered`.

KCOV is also a partial observation of execution:

- Some branch outcomes have no instrumentation witness after compilation.
- Source-line witnesses can be shared by inlined call sites. Order checks are
  within a C function, not a complete cross-function execution trace.
- Unmodeled code is detected within the anchored files: every function of an
  anchored C file that an operation covers must be listed (it owns
  decisions), declared branch-free, or named as a helper cut with its reason
  in `kcov.json` (`helper_cuts`); anything else fails as code outside the
  declared boundary. Header helpers inlined into unanchored code, and
  unanchored files, are outside this rule; coverage is not a completeness
  proof against the C.
- Operand matching is per model obligation: each reported pair must have some
  matching kernel comparison row at its site in the operation. Rows are
  reusable across obligations and surplus kernel rows need no model
  counterpart, so `operand_pairs_matched` counts obligations met and
  `operand_rows_distinct` the distinct kernel rows that met one; neither
  establishes that a repeatedly executed comparison was evaluated the same
  number of times.
- The `wg_observe` observation compares the listeners' datagrams and the
  sender's replies as multisets ordered within a peer session: a stable
  sort by peer key (the listener's family or the reply's source, and the
  message's index word) keeps arrival order within a session and leaves the
  interleaving across peers free. A swap of two datagrams of one session is
  a disagreement; a different interleaving of two peers is not.
- Generated suites are sampled conditional on the mirror's own domain filter:
  the report's `generated` field gives each suite's candidates drawn, in the
  domain, selected, and the rejection reasons with counts, so a domain that
  shrinks is visible even when the agreement count is unchanged.

Declared exceptions such as shared compiler exits and unavailable operands
live in `kcov.json`. Inspect `decision_coverage`, `known_gap_hits` and
`choice_records_skipped` in a check's `report.json` alongside its verdict.
Allocation fault-injection cases marked `domain_extension: "failslab"` are
listed separately: they exercise error paths without claiming the whole trace
is a naturally occurring Linux execution.

Structural review against the C remains necessary. The
[choice-stream design](../docs/2026-10-03-choice-stream-strategy.md) explains
the recording approach; dated design documents contain the detailed rationale
and development history.

The oracle itself is instrumented and supports value steering and virtual
time. Its identity check pins the build; it does not prove that instrumentation
preserves stock behavior. Negative controls and mutants test whether selected
faults are detected, not whether the checker catches every possible defect.
The separate [mirror proofs](../docs/proofs.md) and
[binary experiment](../binary/README.md) have their own statements and trust
boundaries; a differential pass does not establish their premises.
