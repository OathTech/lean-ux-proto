# Paired index-table subsystem: execution report

Status: in progress on `task/binary-pair-runner`, implementing the
[increment charter](2026-10-18-charter-paired-index-subsystem.md).
No complete removal, replacement or shared-reconstruction sequence theorem
is claimed at this checkpoint.

## Start and time limits

[USER 2026-10-18] Resume implementation of the charter within its agreed
scope and record the start so the stopping checkpoint is explicit.

Execution began **2026-10-18 05:54:16 UTC**, from clean charter commit
`95a554c0` (implementation baseline `b630836f`).

- First-day reassessment: **2026-10-19 05:54:16 UTC** (24 elapsed hours).
- Outer planning checkpoint: **2026-10-20 05:54:16 UTC** (48 elapsed hours).
  If incomplete then, report the unfinished obligations and reassess; do not
  silently extend the run or label a smaller result complete.
- Supporting runtime investigation: initially **two hours of focused work**,
  counted separately from proof work, builds and the earlier pause.

Elapsed time includes overlapping activities and is not a person-hour or CPU
estimate. Internal stage completions are progress checkpoints, not stop points.
Substantive correctness or scope blockers are reported when discovered.

## Baseline

Mirror pin `cb2348e` still lags main
`77c9b55594787bd5b371575e2eca1a8d77b3c991`. Kraken is clean at
`7ebba06a30eaf08c10b26b28ca14bfee1c791576`; the binary package uses Lean
v4.35.0. The approved s4 oracle remains read-only. No merge or push.

Existing results and their limits are recorded in the charter and
[previous increment report](2026-10-18-plan-paired-call-increment.md).
The previous increment's external export gate remains pending; it must not
be attributed to the acceptance of the earlier boundary modules.

## Work record

| UTC checkpoint | Activity and result |
| --- | --- |
| 2026-10-18 05:54:16 | Start; inspected the clean tree, charter, pins and executable bucket decoder. First task: reconstruct the bucket after unlinking, then close the full removal call. |
| 2026-10-18 06:25:21 | Reconstruction stage: the concrete predecessor/successor/clear memory effect preserves the executable index reconstruction and ownership flags. Focus and finite list shape are derived from successful decoding. Full machine-call composition is still open. |

Runtime-investigation time used: zero at this checkpoint.

## Completion tracking

| Charter criterion | State |
| --- | --- |
| A: complete removal adequacy and executed witnesses | Open; combined unlink memory effect now restores reconstruction and ownership. Full anchored execution and its envelope remain to be composed. |
| B: complete replacement adequacy and measured reuse | Open |
| C: lookup under the common executable relation | Open; older complete lookup theorem available for adaptation |
| D: finite call-sequence theorem and retained-heap execution | Open |
| E: actual mutator captures, trust checks and cost report | Open |

Final theorem statements, named hypotheses, measurements, findings and
reproduction commands will replace these open entries as the work proceeds.

## Reconstruction stage

`UnlinkFocus.reconstruct` and `UnlinkFocus.ownership` prove the effect of
the concrete byte stores in `unlinkMemory`: overwrite the predecessor,
repair a non-NULL successor, and clear the removed owner's predecessor word.
They cover all list positions, including sole entries, and frame every
other bucket, owner peer word and count. `reconstruct_focus` extracts the
physical focus from a source member and successful reconstruction; it does
not ask the caller to supply the intended list shape.

The runtime `reconstruct` definition and source `target` are unchanged.
`reconstruct_normal` proves a list-traversal normal form of the existing
imperative decoder. The finite chain and neighbour lemmas invert that
decoder and return to it after the splice. `bucket_erase` is used by the
concrete bucket proof; local after-state word equations are discharged by
`unlink_word` and the checked storage separation, not assumed as a future
successful decode.

[AGENT 2026-10-18] Add `storageCheck` to removal's physical readiness. It
checks separation of the table, each embedded entry and each peer-count
field, including separation within a containing peer allocation. These
immutable address checks support the actual store frame. They impose no
condition on membership, peer words or count values. This refinement was
identified during proof work, then exercised by the paired runner; it was
not a counterexample discovered first by workload execution. It is outside
the source observation and does not change the dead-peer domain.

Validation at this stage:

- Targeted Lean builds pass with standard axioms and no new warnings.
  Inherited warnings remain visible.
- All 54 paired removal calls pass, totalling 4,550 executed instructions
  under two undefined-value seeds. The repeated-removal and collision-chain
  cases retain their heaps. Paired runtime was 1.663 seconds on this shared
  host; this is not an optimization claim.
- The selected recorded-prefix calls still pass the independent three-way
  coverage/decision comparison. They are source-materialized entries,
  not captured mutator memory and not execution of intervening callers.
- The stale-owner rejection remains exercised. A targeted count/entry
  overlap is rejected by the new storage check before reconstruction.
- Fresh local kernel replay passed for `PairUnlinkReconstruct` and
  `PairUnlinkOwnership`. External acceptance is not
  claimed for this increment.

The first reconstruction stage took about 31 elapsed minutes from the
recorded start, including overlapping builds and validation. No additional
instruction coverage or complete new function is claimed: connecting this
memory effect to the whole compiled removal remains the next task. Routine
Lean elaboration failures were fixed before the passing builds. An initial
fresh-replay command incorrectly supplied two modules; it failed explicitly
and was corrected to one module per invocation.

`PairIndexFrame` additionally derives preservation of reconstruction and
ownership from byte equality on the finite index-storage cover. It is the
frame needed to compose the unlink effect with stack, coverage and preempt
updates; it adds no source-observation clause.

Reproduce from the worktree root (with `capped` on shared boxes):

```sh
(cd binary && capped lake build binary-pair-remove PairUnlinkOwnership)
capped python3 binary/remove_probe.py --check .artifacts/check/binary-remove-20261018
(cd binary && capped lake env leanchecker --fresh PairUnlinkOwnership)
```

The recording is ephemeral; its regeneration command is in the previous
increment's removal calibration. No runtime-optimization budget has been used.
