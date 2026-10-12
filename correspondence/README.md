# How the model is checked against Linux

Lean-ux aims to preserve the data structures and control-flow choices of the
configured Linux code, while abstracting away C memory representation. The
checker tests this correspondence on operation traces; it does not prove it.
All checks refer to the kernel build pinned by
[`identity-x86_64-net-choice.txt`](../kernel/identity-x86_64-net-choice.txt).

## Where to look

| Part | Location |
| --- | --- |
| Kernel-shaped state, with identities in place of pointers | [`Leanux/Kernel/Defs.lean`](../Leanux/Kernel/Defs.lean), [`Leanux/WG/Types.lean`](../Leanux/WG/Types.lean), [`Leanux/WG/State.lean`](../Leanux/WG/State.lean) |
| Functions following the C, with source sites and abstraction boundaries in comments | [`Leanux/FS/`](../Leanux/FS/), [`Leanux/WG/`](../Leanux/WG/) |
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

## Limits of the evidence

The model covers selected paths of a single-CPU kernel. Environment assumptions
and operations below the modeled boundary are explicit contracts, not checked
C implementations. Generated candidates outside the modeled domain are
filtered before guest execution and reported in `domain_filtered`.

KCOV is also a partial observation of execution:

- Some branch outcomes have no instrumentation witness after compilation.
- Source-line witnesses can be shared by inlined call sites. Order checks are
  within a C function, not a complete cross-function execution trace.
- Unmodeled code is detected only where it intersects the checker's anchored
  files, functions and spans; coverage is not a completeness proof.
- Operand matching does not establish that a repeatedly executed comparison
  was evaluated the same number of times.

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
