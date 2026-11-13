# Independent review of the binary remediation landing

Review scope [AGENT 2026-11-13]: the complete difference from main
`9ca4b0655d8a886dc01656bfedbc2581c388fc1e` to candidate `28b36383`, followed
by disposition delta `0808df34`. The reviewer inspected the operational
observer, capture selection and provenance, endpoint comparison, interpreter
history selection, diagnostics, admission inventory and archive exclusions.
The review was not confined to newly changed lines.

## Findings and disposition

**F1 — High: inherited capture-extent defects remain outside the index
repair.** `PairAllowedipsCapture.run` compares the supplied header/return
blocks and applies trie reconstruction, but does not enforce the collector's
required ranges. A returned KCOV range can be omitted without affecting that
reconstruction. `PairInsertCapture.run` and `randomReturn` likewise compare
only supplied endpoint blocks. `PairAllowedipsInsertCapture.run` has no
native memory check after `compareEndpoint`; omitting its entire returned
block array removes that memory comparison. Its allocator protection check
also iterates supplied bytes. These are code-inspection findings; this review
did not reproduce those three protocols on altered native captures.

The defects predate this increment. Moving the index guard into the generic
comparator would not repair them correctly: allowed-IPs entry bulk data and
bounded return/header spans have different protocols. Each needs its own
expected extents and genuine positive and omission tests. The current
README and admission inventory now name these as open checker defects.
This is a documented deferral, not a fix. Intact historical captures do not
become incomplete because an incomplete file could have been accepted.

**F2 — Low: obsolete assessment wrapper contradicts the current CLI.**
`assessment/capture_lookup_full.py` still claimed that the normal collector
could not request full coverage and silently overrode its new
`--partial-coverage` option. Delta `0808df34` removes the redundant helper
from this landing and updates the reproduction command to the normal full
collector. The original research branch retains the earlier experiment.
Resolved by inspection of that delta.

## Independent validation

The reviewer used a private worktree and private locked Kraken bootstrap.
The runtime build passed all 477 jobs without warnings. The Python checks
passed: 38 binary tests and six C2 controls. The endpoint interpreter check
accepted complete extents and consistent overlap and rejected all twelve
invalid endpoint/extent controls. Whitespace validation passed.

The capture worker supplied an immutable fresh native hit capture for
`d1_second_response`. The reviewer independently replayed it with the
corrected executable: both seeds, 0 and `18446744073709551615`, passed
`IndexLookup.callBoundary`, 506 instructions, 189 reads, 74 writes and
33,624,268 returned bytes. The entry preempt count was `0x80000000`.
This replay took 3 minutes 22 seconds and peaked at 8,121,628 KiB RSS under
a 16 GiB cap. This is an independent replay of the worker's capture, not
another independent guest boot.

The reviewer then removed only the returned 33,554,432-byte coverage block,
keeping the entry and every other field unchanged. The same corrected
runner rejected this actual-capture mutation with exit 1 and
`FAIL: capture.return-extent`, producing no success output. The test was
performed through the full lookup executable, not only the extent helper.

Reproduction from a task worktree, with the saved s5 image and a host Python
providing the documented dependencies:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
binary_python=$(command -v python3)
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
CAPPED_MEM_MAX=16G cap scripts/in-bundle lake -d binary build \
  binary-pair-capture binary-pair-mutator-capture \
  binary-replacement-observe binary-replacement-admit
CAPPED_MEM_MAX=2G cap scripts/in-bundle "$binary_python" -B -m unittest discover -s binary -p 'test_*.py'
CAPPED_MEM_MAX=2G cap scripts/in-bundle "$binary_python" -B -m unittest discover -s binary/remediation -p 'test_c2_memory.py'
CAPPED_MEM_MAX=2G cap scripts/in-bundle lake -d binary env lean --run binary/remediation/CaptureEndpointChecks.lean
```

For a fresh native lookup, use the
[full-allocation capture recipe](2026-11-13-binary-remediation-first-batch.md#reproduce-the-lookup-experiment)
with `d1_second_response`, then run `binary/pair_capture.py` to prepare the
same-boot `replay-input.json` and `probe/layouts.json`. Keep the original
snapshot unchanged. The following generates an omitted-range control;
substitute that capture directory for `lookup_capture`:

```sh
lookup_capture=.tmp/review-hit
CAPPED_MEM_MAX=2G cap "$binary_python" -B - "$lookup_capture" <<'PY'
import json
from pathlib import Path
import sys
capture = Path(sys.argv[1])
snapshot = json.loads((capture / 'snapshot.json').read_text())
address = snapshot['initial']['coverage']
removed = [b for b in snapshot['returned']['blocks'] if b['address'] == address]
assert len(removed) == 1
assert len(removed[0]['bytes']) == snapshot['initial']['capacity'] * 8
snapshot['returned']['blocks'] = [b for b in snapshot['returned']['blocks']
                                if b['address'] != address]
(capture / 'omitted-coverage.json').write_text(json.dumps(snapshot) + '\n')
PY
CAPPED_MEM_MAX=16G cap binary/.lake/build/bin/binary-pair-capture \
  "$lookup_capture/replay-input.json" "$lookup_capture/snapshot.json" \
  "$lookup_capture/probe/layouts.json"
CAPPED_MEM_MAX=16G cap binary/.lake/build/bin/binary-pair-capture \
  "$lookup_capture/replay-input.json" "$lookup_capture/omitted-coverage.json" \
  "$lookup_capture/probe/layouts.json"
```

The last command must fail with `capture.return-extent`; its nonzero exit is
the expected control result. Captures, altered inputs and raw logs are
ephemeral.

The review independently checked that the mirror, evaluator, harness, kernel,
corpus and scripts are unchanged from the observer revision `ffb3d8df`.
The proof tree, binary trust surface and dependency pins are unchanged from
main. Consequently the previously reported full differential run and
controls concern the same operational implementation; they were not rerun
by this reviewer. The coordinator's gate and fresh kernel replay remain
separate reported validation, not independent executions by this reviewer.

## Claim boundaries

The optional observer only appends pure diagnostic state. No operational
choice consumes that output; speculative worlds discard their observations
with the world. Its enabled/disabled check compares named finite projections,
not function extensionality. The replacement pilot independently reaches the
original caller and then checks a bounded Device projection; the Python
driver is necessary for the same-boot record and dispatch claim. The Lean
admission executable alone does not supply that provenance.

The history selector changes retained interpreter snapshots, preserving the
instruction and access logs and live lookup assertions. The new extent guard
matches the index collector's exact entry/return protocol. The C2 tool cannot
return admission success: an observed failure exits 1, and absence of a
found counterexample remains incomplete with exit 2.

No archived whole-driver theorem or supplied-answer model is imported. No
new theorem or scalable composition result is established. The separate
mirror proof tree is explicitly lagging the observer change. Full
replacement postconditions, native memory interpretation and universal
environment/service assumptions remain unresolved.

## Recommendation

The reviewed increment is suitable to present for main signoff as scoped
capture/checker repairs, a bounded source-entry observation and honest
diagnostics. No further defect in those new paths was found by this review.
F1 remains a high-severity inherited defect and must be visible in that
signoff request. This recommendation does not establish correctness or
complete admission of the existing binary package; Stage 1 remains open.
