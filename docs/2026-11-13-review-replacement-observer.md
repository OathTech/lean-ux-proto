# Independent review: replacement source-entry observer

Review of `ffb3d8df`, provenance driver `064b3fa8`, and correction
`5530a339`, with the native collector changes `30ba728b` / `5ac334e0`
and final documentation `e9979ed3`.
Work and experiments used a private review worktree, one heavy job at a
time under an 8 GiB cap. Shared captures were read-only inputs. No
implementation, oracle, harness, shared dependency or main-branch changes
were made by the reviewer.

## Findings

### F1 — High: omitted return memory produced a false pass; fixed

The streaming refactor in `PairMutatorCapture.replayAt` (current
`binary/PairMutatorCapture.lean:116`) removed the
independent assertion on captured return memory and relied on
`Capture.compareReturn`. That comparator iterates only the supplied
`returned.blocks`; it does not establish their completeness.

An independent experiment on a private copy of the genuine discovery
capture changed only `returned.blocks` to `[]`. The pre-fix executable
returned `predicate-and-replay-pass`: 115 instructions at both undefined
value seeds, with **zero compared bytes** at each seed. Its existing
changed-byte and missing-PC controls still passed. Thus omission could
erase the native memory evidence without rejecting admission.

Remedy: require the collector's complete return extent before streaming,
or retain an equivalent independent native post-state assertion. Commit
`5530a339` implements the former at `binary/PairMutatorCapture.lean:92` in
[`checkReturnExtent`](../binary/PairMutatorCapture.lean), called at the
start of `replayAt`: the nonempty entry address/length array must match
the return array exactly. The corrected private executable rejects the
identical malformed capture with exit 1 and `capture.return-extent`.
The fix also covers the older removal/replacement runner sharing this
path. Validation of the full capture and extent controls is recorded below.

### F2 — Low: reproduction selected the wrong Python; fixed

The initial `binary/remediation/replacement-source.md:39` commands selected
`python3` after entering `scripts/in-bundle`. In this environment that
interpreter lacks pyelftools: the advertised unit command failed with
five module-import errors. Selecting the host interpreter before entering
the bundle, as the existing binary reproduction instructions require,
ran all 38 tests successfully. Documentation commit `e9979ed3` uses
that established interpreter-selection pattern. The independent combined
run also used it successfully, with no shared environment change.

### F3 — Scope: complete theorem-postcondition admission remains open

[`replayAt`](../binary/PairMutatorCapture.lean), lines 116–149, evaluates the exact
`Replace.callBoundary`, source result, index reconstruction/ownership,
coverage readiness and native/interpreter endpoint equality. It does not
evaluate the full `Replace.Post` in
[`PairReplaceAdequacy`](../binary/PairReplaceAdequacy.lean), line 30, and its
first-return counterpart: in particular, `MemoryReady`, `EqualOutside`
and `KindFrame` are not jointly executed as that postcondition. Native
endpoint equality does not itself test those predicates, and bytes outside
the captured virtual ranges remain unobserved.

The report and register at `e9979ed3` retain these obligations explicitly. This
pilot can establish the selected source-entry match and its checked replay;
it cannot be called complete admission of the existing theorem conjunction
or completion of remediation Stage 1. Universal service/permission
obligations and general caller composition also remain unresolved.

## Independent assessment

The observer is attached immediately before the original replacement call,
after the caller's keypair initialization and peer dereference. It copies
the current Device, arguments, counters and remaining records, then only
appends an optional pure-state journal. Inspection found no operational
reader of that journal. Discarded speculative worlds discard their copied
observations. Enabled/disabled checkpoint equality is a finite comparison
of the fields named by the implementation, not full World equality.

The source executor uses the original caller and same-boot resolved records;
it does not reconstruct the expected index table from native memory. The
admission executable uses the observed Device, with peer public keys and
peer/keypair allocation IDs naming objects. Its remaining World fields
come from the completed operation, but the selected predicate and local
index mutator use only the stated Device projection and decision output.
That limitation is material and should remain explicit.

The driver independently checks the stopped sequence-counter bytes, dropped
counter, active PC-mode area, section function/unit/start, operation and
all-call ordinal, exact raw record prefix and exact source suffix. Its
bounded context rejects suspended/interleaved dispatches and nonzero
ordinals. It requires successful provenance and `predicate-and-replay-pass`
before returning overall success; the Lean executable alone is not a
provenance checker. These are suitable checks for the declared single-call
pilot, not continuous observation of a lifecycle or joined sequence.

## Validation

* Private builds of both observer/admission executables passed (471 jobs);
  rebuilding the corrected shared replay passed. The root model executable
  also built (132 jobs).
* All 38 binary Python tests passed using the host Python with pyelftools.
* The malformed native return experiment and corrected rejection are
  described in F1; no failed semantic experiment was retried.
* The first combined-driver invocation failed on a missing private
  `leanux-model` executable before source execution. After building that
  documented prerequisite locally, it was restarted once.
* The corrected combined driver passed on the unchanged discovery capture:
  one observation; three equal enabled/disabled checkpoints; native sequence
  47, section start 40 and eight active-area records; 11 consumed source
  records and the exact 13-record remainder. Both seeds replayed 115
  instructions and compared 33,625,512 bytes, rejecting three entry
  mutations and four return mutations per seed. The full driver took
  137.55 seconds with maximum process RSS 5,203,036 KiB under the 8 GiB cap.
* `CaptureEndpointChecks.lean` passed complete extent/consistent overlap
  and rejected all 12 invalid endpoint/extent cases.

With the pinned setup, `cap` function and `binary_python` selection in
[the reproduction instructions](../binary/REPRODUCING.md), the independent
combined invocation used:

```sh
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B \
  binary/remediation/replacement_source_capture.py \
  --input INPUT.json --capture CAPTURE --operation 2 --call-index 0
cap scripts/in-bundle lake -d binary env lean --run \
  binary/remediation/CaptureEndpointChecks.lean
```

Here `INPUT.json` was the prepared discovery workload; `CAPTURE` was a
private directory linking the discovery capture's snapshot, layout and
boot log read-only, so the driver's temporary input remained private.
For the omission experiment, copy `snapshot.json` into a private directory,
replace only `returned.blocks` by `[]`, and invoke
`binary-replacement-admit INPUT.json SNAPSHOT.json LAYOUTS.json 2 0` with
the same-boot prepared input. The pre-fix revision accepts it; `5530a339`
rejects it. No generated captures or logs are retained in this report.

No new native boot, full differential campaign or proof-tree acceptance
was performed by this reviewer. The separate mirror proof tree is lagging
the observer's operational-mirror change. The binary build is not evidence
of renewed external proof acceptance or discharge of universal hypotheses.

No further implementation defect was found within this pilot's declared
scope after F1's correction. The independent entry observation and checked
native replay are useful progress; F3's unadmitted clauses still prevent
claiming complete replacement-headline admission or commissioning a proof
or composition that assumes those obligations have been discharged.

The final documentation revision correctly records the demonstrated false
pass and its correction, interpreter selection, full-postcondition limit
and mirror-proof lag. Broader mirror validation was still in progress at
this review's completion; its eventual result is a separate claim point.
