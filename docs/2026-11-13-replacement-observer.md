# Replacement source-entry observer: Stage 1 pilot

This continues the [remediation plan](2026-11-13-binary-remediation-plan.md)
on `feature/binary-remediation-20261113`, following the
[completed-boundary diagnosis](2026-11-13-replacement-source-cut.md).
Implementation choice [AGENT 2026-11-13]: observe the original caller with
an optional pure output journal, preserve exact record provenance, and run
the existing replacement predicate against independently predicted state.
No theorem or composition is added.

## What each part does

1. **Reach the source call.** `Leanux.Observation.replacementEntry` appends
   the actual Device, arguments, allocation counters, Steps, remaining
   records and dispatch bookkeeping immediately before the original
   `indexReplaceHandshake` call, after `peerDeref`. Execution then continues
   normally. The hook consumes no records and changes no branch. It is
   disabled by default. Its `StateT` journal is discarded with discarded
   speculative consistency trials; it is not an IO callback.
2. **Match the invocation.** The native collector selects by call ordinal
   within the operation before inspecting linkage. It captures the full
   KCOV allocation and stopped sequence/dropped-counter bytes. The driver
   matches the same boot's stream, sequence, dispatch function, work unit
   and section start, then checks the exact source record suffix. It never
   normalizes passive records to obtain a match. This pilot requires one
   replacement, ordinal zero, in an unambiguous handshake receive-worker
   section; nested or suspended contexts are refused.
3. **Check entry and return observations.** The expected Device comes from that source
   observation. Public keys and peer/keypair allocation IDs name objects;
   native table values, owner words and counts do not supply expectations.
   The executable checks actual arguments and `Replace.callBoundary`,
   executes the existing source mutator, and replays the complete native
   instruction/return capture at two undefined-value seeds. PCs, registers,
   flags and every return byte are compared. The return must contain the
   complete entry address/length extent before streaming comparison.
4. **Challenge the checker.** Enabled and disabled source replay must have
   equal returns, Device, counters, complete Steps, remaining records,
   environment call counts, extra output and user output. Malformed input,
   selection, source-state and return controls must fail. A fresh held-out
   capture follows the fixed checker, with independent implementation review
   and the existing mirror/binary validation channels.

The predicate reads `World.wg.dev`; the local index mutator uses that store
plus normal decision output. Other World fields are unused scaffolding
from the completed containing execution. This is not complete World
equality or a comparison of every Device field: the existing predicate
checks its index/owner/refcount and machine-context projection. Function
fields are not claimed extensionally equal by the observer comparison.

## Validation

Discovery and fresh held-out combined validation pass on checker
`5530a339`. Independent review and broader mirror validation are still in
progress. Both boots complete all six operations and exit successfully.

The discovery source reaches one entry and consumes 11 of 24 records,
retaining the exact 13-record suffix. Three completed-operation checkpoints
agree with observation disabled. The native record frontier is 47, with
eight active-area records beginning at receive-worker section 40. The
work-unit address agrees. The predicate and return replay pass at both seeds
on both captures:
115 instructions and 33,625,512 compared bytes each, including 4,194,304
KCOV words. The exact record counts and section identity match in both
boots; their independent random index draws differ.

| Capture | Index draw | Combined runtime | Maximum process RSS |
| --- | ---: | ---: | ---: |
| Discovery | 2076239516 | 135 seconds | 5,193,964 KiB |
| Held-out | 2007342028 | 141 seconds | 5,191,416 KiB |

Both runs use a 16 GiB cap. Each rejects three actual entry mutations
(missing identity, NULL predecessor and erased source table), and four
return mutations at each seed (missing/truncated memory, missing PCs,
changed byte). The Python suite passes 38 tests, including 12 provenance
tests. The small Lean endpoint test rejects 12 invalid cases. The
source observer separately rejects a missing observation and wrong ordinal.

Review demonstrated a false pass in the initial streaming refactor: a
private copy of the real capture with no returned memory blocks passed
both seeds with zero compared bytes. Commit
`5530a339` requires the exact captured extent and tests empty, missing,
truncated and relocated return ranges. Final admission uses that correction.
The earlier successful complete capture did not validate the defective
checker against incomplete captures.

The binary trust gate passes its unchanged 71-headline surface with only
standard axioms. Fresh `leanchecker --fresh PairMutatorCapture` replay also
passes over the corrected implementation. Image and Kraken pins are
unchanged. The hook changes the operational mirror at
`ffb3d8df`; the separate mirror proof tree has not been carried to this
revision and is lagging. Its historical checkpoints remain historical.
Binary runtime checks and local kernel replay do not establish acceptance
of that proof tree or the sandboxed external proof-acceptance gate.

## Limits and next work

This is successful replacement inside `c_remove_after_handshake`, under the
existing single-CPU sequential-call setup. Removal/insertion callers,
general lifecycles, concurrent interference, universal permissions/services,
lookup transport's joint representation/separation premises and the
archived C2 frame remain conditional or unresolved. See the
[current register](proofs.md#current-admission-inventory-2026-11-13).

Specifically, this runner checks `Replace.callBoundary`, the result byte,
`Remove.assertAt`, coverage readiness and interpreter/native endpoint
equality. It does **not** evaluate the full `Replace.Post` conjunction in
`PairReplaceAdequacy.lean`: `MemoryReady`, `EqualOutside` and `KindFrame`
remain unadmitted, as do internal invariants and universal service/permission
assumptions. Exact captured return equality is not a substitute for checking
those clauses. This is progress on independent caller-entry admission, not
complete admission of the replacement headline theorem or completion of
Stage 1 for the package.

## Reproduction

Use the private dependency and saved s5 image setup in
[binary/REPRODUCING.md](../binary/REPRODUCING.md). Select a host Python with
pyelftools; export both `LEANUX_BINARY_KERNEL_DIR` and `LEANUX_KERNEL_DIR`
as documented. Prepare the independent recording and probe with the
[source-cut recipe](2026-11-13-replacement-source-cut.md#reproduction).
Then, from the task worktree, using those input/check paths:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
binary_python=$(command -v python3)
cap scripts/in-bundle lake -d binary build binary-replacement-observe binary-replacement-admit
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B binary/capture_index_mutator.py \
  --anchor replace --call-index 0 --input .tmp/source-cut/probe/input.json \
  --check .artifacts/check/source-cut --operation 2 \
  --out .tmp/source-cut/discovery-observed --finish-workload
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B \
  binary/remediation/replacement_source_capture.py \
  --input .tmp/source-cut/probe/input.json \
  --capture .tmp/source-cut/discovery-observed --operation 2 --call-index 0
cap scripts/in-bundle "$binary_python" -B -m unittest discover -s binary -p 'test_*.py'
cap scripts/in-bundle lake -d binary env lean --run binary/remediation/CaptureEndpointChecks.lean
```

Repeat capture/admission into a fresh held-out directory after fixing the
checker. The combined Python driver is the claim point; the Lean predicate
executable alone does not establish record provenance. Raw captures and
reports are ephemeral; preserve conclusions and commands, then regenerate.
